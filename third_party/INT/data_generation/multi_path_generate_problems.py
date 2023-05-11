import argparse
import json
import os
import pickle
import random
import shutil
import time
from concurrent.futures import ProcessPoolExecutor
from copy import deepcopy

from data_generation.combos_and_orders import get_combo_order_info, randomize_one_axiom_order
from data_generation.forward2backward import forward_to_backward
from data_generation.utils import steps_valid, make_up_condition, \
    generate_valid_steps, Dataset, proof_agrees_with_specs, initialize_prover, gather_available_entities
from proof_system.all_axioms import all_axioms
from proof_system.proof_graph import ProofGraph, ProofNode
from proof_system.utils import is_all_operands_constant, sample_ls
from visualization.seq_parse import my_logic_statement_to_seq_string
from proof_system.smt_solver import smt_solver
from data_generation.graph_forward2backward import graph_forward_to_backward
import pdb
import misc.global_var as global_var
import numpy as np
random.seed(0)
np.seterr(all='ignore')

# 遍历 how_to_extend["makeup_config"] 中的所有配置，为每个条件生成一个命题。
# 将所有命题添加到 make_up_conclusions 列表中，并调用 prover.add_logic_statements() 将它们添加到 prover 中。
# 将 make_up_conclusions 中所有命题的名称添加到 premise_names 列表中。
# 根据添加到 prover 中的命题，通过调用 how_to_extend["operand_retrieval"]() 来获取操作数。
# 返回操作数（operands）和未使用的原子实体（no_atom_ents）。
def get_operands_when_making_up_conditions(how_to_extend, make_up_conclusions, prover, premise_names, no_atom_ents, check_solver):
    # makeup_config 是 一个列表，列表里面的每个元素都是一个字典
    # 字典包括requirement_type（比如：Equivalent），还有a，b
    # how_to_extend本就是axiom的extend_core_gt的返回值
    for config in how_to_extend["makeup_config"]:
        new_atom_ent = config.get("new_iv", True)
        # 这个makeup_condition就很奇怪，它生成一个新的entity：c,然后返回一个
        # Equvalent(add(a+c), b), 编出来一个这么个条件之后，就加进了prover里面，就很诡异
        makeup = make_up_condition(
            config["requirement_type"],
            config["a"],
            config["b"],
            no_atom_ents, new_iv=new_atom_ent)
        makeup_conclusion, no_atom_ents = makeup["conclusion"], makeup["no_iv"]
        make_up_conclusions.append(makeup_conclusion)
    
    cnt_constraint = 0
    for con in make_up_conclusions:
        try:
            constraint_status, constraint_bool = check_solver.add_constraint(con)
        except:
            for i in range(cnt_constraint):
                print('exception!!')
                check_solver.pop()
            assert check_solver.check() != 'unsat'
            return None, None
        
        if constraint_status:
            cnt_constraint += 1
        
        if constraint_bool == 'Unknown':
            if check_solver.check() == 'unsat':
                for i in range(cnt_constraint):
                    check_solver.pop()
                assert check_solver.check() != 'unsat'
                return None, None
        elif constraint_bool == 'False':
            for i in range(cnt_constraint):
                check_solver.pop()
            assert check_solver.check() != 'unsat'
            return None, None

    prover.condition_ids.extend(prover.add_logic_statements(make_up_conclusions))
    prover.update_conditions()
    for con in make_up_conclusions:
        premise_names.append(con.name)
    
    make_up_conclusions = [prover.ls_id2ls[prover.ls_name2id[con.name]] for con in make_up_conclusions]
    # 这个operand_retrieval的返回值其实就是把extend_core_gt对应的axiom的operands
    # 和makeup_conclusions[0]的operands给连起来，其实也就是获得了所有的operands
    # print(f"make_up_conclusions:{make_up_conclusions[0].name}")
    operands = how_to_extend["operand_retrieval"](make_up_conclusions) # 将需要的operands取出来了

    return operands, no_atom_ents


def produce_operands_info_for_ordinary_lemma(prover, lemma, core_gt, entities, do_transform_this_time,
                                            transformed_solutions, premise_names, no_atom_ents, check_solver):
    # 这个extend_core_gt有点奇怪阿
    how_to_extend = lemma.extend_core_gt(core_gt, entities, transform_gt=do_transform_this_time)
    # how_to_extend就是一个字典, 包括action, makeup, operands, substitution_retrieval, original_coding, operands是一堆entity
    
    if how_to_extend["action"]:
        if "original_coding" in how_to_extend:
            original_coding = how_to_extend["original_coding"]
        else:
            original_coding = lemma.original_coding()

        side = None
        if "transformed_side" in how_to_extend:
            do_transform_this_time = True # 对equivalent的哪边应用lemma
            side = how_to_extend["transformed_side"]

            if "circle_back_names" in how_to_extend:
                # Avoid commutativity switching things back and forming an infinite loop
                if (lemma.name, tuple(how_to_extend["circle_back_names"])) in transformed_solutions:
                    how_to_extend = lemma.extend_core_gt(core_gt, entities, transform_gt=False)
                    do_transform_this_time = False
                    original_coding = lemma.original_coding()
                else:
                    transformed_solutions.add((lemma.name, tuple(how_to_extend["circle_back_names"])))
        else:
            do_transform_this_time = False

        if "add_condition" in how_to_extend:
            raise NotImplementedError

        # Make up conditions
        # 编造条件，这种做法通常用于解决证明在当前命题和已有条件下无法被证明的问题，编造更多的条件用于推理
        # 该函数将修改列表make_up_conclusions以包含新的条件，并返回更改后的operands（操作数）。
        make_up_conclusions = list()
        # 这里的operands是指一些field_axioms,比如：SquareDefinition
        if how_to_extend["makeup"]:
            operands, no_atom_ents = get_operands_when_making_up_conditions(
                how_to_extend, make_up_conclusions, prover, premise_names, no_atom_ents, check_solver)
            if operands == None:
                return None
        else:
            operands = how_to_extend["operands"]
        
        return how_to_extend, operands, original_coding, side, do_transform_this_time, no_atom_ents, make_up_conclusions
    else:
        return None


def produce_operands_info_for_substitution(prover, result, how_to_extend, make_up_conclusions):
    # Apply substitution axiom, if required
    if "substitution_retrieval" in how_to_extend:
        proof_conclusion = prover.ls_id2ls[result["conclusion_ids"][0]] #把应用lemma后，新的conclusion拿出来了
        # If substitution is required after theorem application
        operands = how_to_extend["substitution_retrieval"](make_up_conclusions, proof_conclusion) # 返回proof_conclusion的operands和定理应用时的core_gt的operands
        lemma = all_axioms["EquivalenceSubstitution"]
        return lemma, operands
    else:
        return None, None


def apply_ordinary_lemma(probability_no_transform, transform_gt, prover, lemma, core_gt, entities,
                        transformed_solutions, premise_names, no_atom_ents, steps, check_solver):
    # Decide whether to do transformation or not according to a 1-e/e probability
    # Default e=0
    do_transform_this_time = False if random.random() < probability_no_transform else transform_gt
    # 我感觉这个函数好像是说，看看这个lemma能怎么用，如果能用，就返回一个action_info
    # action_info中最重要的是operands，就是这个lemma要作用在哪些operands上
    # 然后再proceed_step中的apply时，应用了这个lemma
    action_info = produce_operands_info_for_ordinary_lemma(prover, lemma, core_gt, entities, do_transform_this_time,
                                                            transformed_solutions, premise_names, no_atom_ents, check_solver)
    
    # There's no action that can be performed at this time, therefore an invalid problem
    if action_info is None:
        return
    how_to_extend, operands, original_coding, side, do_transform_this_time, no_atom_ents, make_up_conclusions, \
        = action_info
    # Apply ordinary.sh axiom step
    step = {
        "observation": prover.get_observation(),
        "lemma": lemma,
        "input_entities": operands,
        "original_coding": original_coding,
        "transform_gt": do_transform_this_time,
        "transformed_side": side,
        "custom_function": how_to_extend.get("custom_function", None)
    }
    # 这里的result是一个字典, 包括conclusion_ids, assumption id
    # core_gt经过一步proof之后, 得到一个新的core_gt
    result, core_gt = proceed_step(step, prover, steps)
    return result, core_gt, how_to_extend, make_up_conclusions

# 在谓词逻辑中，Substitution 通常用于进行谓词逻辑表达式的求值。Substitution 是将符号替换为其他符号，以便在推理过程中生成新的表达式。
# 在谓词逻辑中，Substitution 可以被视为将表达式中的变量绑定到特定实体或常量（即常规数学计算中的等价物）上。
def apply_substitution(prover, steps, result, how_to_extend, make_up_conclusions):
    # Apply substitution step
    if result is None:
        return
    lemma, operands = produce_operands_info_for_substitution(prover, result, how_to_extend, make_up_conclusions) # 这个返回的lemma是那个EquivalenceSubstitution
    # print(f"operands:{[ope.name for ope in operands]}")
    
    if lemma is None:
        return False, False
    # Need to do substitution
    step = {
        "observation": prover.get_observation(),
        "lemma": lemma,
        "input_entities": operands
    }
    result, core_gt = proceed_step(step, prover, steps, mode="substitution") # 这个mode似乎并没有用
    
    # The substitution fails, therefore problem invalid
    if result is None:
        return
    return core_gt, result

# 这里的result是一个字典，包括conclusion_ids, assumption id
# core_gt经过一步proof之后，得到一个新的core_gt
def proceed_step(step, prover, steps, mode="ordinary.sh"):
    """
    Given a proof step, apply it to the prover, and add it to all the steps collected, if it proceeds successfully
    :return: the result of the proof step application, and the new core ground truth
    """
    # 这里面的assumption index也非常让人迷惑啊
    # input_entities就是那些a,b,c之类的
    # result 里面是一堆assumption id, conclustion id之类的东西，就是把lemma应用到刚刚找出来的operands上
    result = prover.apply_theorem(step["lemma"], step["input_entities"])
    
    # 这个好像就是判断一下状态
    interpretation = prover.interpret_result(result)
    if interpretation == "REWARD_ASSUMPTION_INVALID":
        raise AssertionError
    elif interpretation == "REWARD_DUPLICATED_RESULTS":
        if mode == "ordinary.sh":
            return None, None
        core_gt = False
    elif interpretation == "REWARD_THEOREM_PROCEEDED":
        steps.append(step)
        # 完成一步证明之后，gt增加了
        core_gt = prover.ls_id2ls[result["conclusion_ids"][0]] # 把新的conclusions里的第一项拿出来，目前来看似乎也一般只有一个conclusion
    else:
        print(interpretation)
        raise NotImplementedError
    return result, core_gt


def add_premises_to_each_step(prover, steps, core_gt):
    # Get conditions
    conditions = [prover.ls_id2ls[con_id] for con_id in prover.condition_ids]
    # Add made up conditions to each step
    if len(steps) > 0:
        # For evaluation purpose
        for s, step in enumerate(steps):
            gt_names = {
                gt.name for gt in step["observation"]["ground_truth"]
            }
            for con in conditions:
                if con.name not in gt_names:
                    steps[s]["observation"]["ground_truth"].append(con)
        for j in range(len(steps)):
            core_gt_copy = core_gt
            steps[j]["observation"]["objectives"].append(core_gt_copy)
    return conditions

def get_a_forward_problem(atom_ents, prover, axiom_order, no_atom_ent_max=150, no_node_max=1500, entity_length_limit=15,
                        transform_gt=True, probability_no_transform=0.0, **kwargs):
    """
    Generate a theorem and its forward proof
    :param atom_ents: atomic entities(like a, b, c)
    :param prover: the forward prover used to write the proof
    :param axiom_order: the order in which axioms should be applied
    :param no_atom_ent_max: the limit of atomic entities used
    :param no_node_max: the limit of graph nodes allowed
    :param entity_length_limit: the limit of the length of entities
    :param transform_gt: whether to allow transforming the core ground truth or only extending it
    :param probability_no_transform: the probability of not doing transform_gt
    :param kwargs: other keyword arguments
    :return: the forward proof steps of the theorem generated
    """
    # Initialize prover and starting conditions
    steps = []
    premise_names = list()
    transformed_solutions = set()
    problem_graph = ProofGraph()
    used_atom_ents, forward_prover = deepcopy(atom_ents), deepcopy(prover)
    check_solver = smt_solver()
    for gt in forward_prover.get_ground_truth():
        _, constraint_bool = check_solver.add_constraint(gt)
        if constraint_bool == 'False':
            return
    
    if check_solver.check() == 'unsat':
        return
    
    no_atom_ent = sum([1 for ent in atom_ents if not ent.is_constant]) # 获取所有不是常数的entity的个数
    for axiom_name in axiom_order:
        # Apply ordinary.sh lemma
        # 奥 这个lemma就是从axioms中拿出来的对应的lemma，相当于实例化了一下
        # print(f"axiom_name:{axiom_name}")
        lemma = all_axioms[axiom_name]
        # 这个好像就是从所有的gt,每个gt是一个logic_statement,从每个statement树中选出来所有的entities, 目前而言是一堆a,b,c这种东西
        entities = gather_available_entities(forward_prover, entity_length_limit)
        if lemma.input_type == 'equality':
            core_gt = sample_ls(problem_graph, forward_prover.get_equality_ground_truth(), 0.9)
            # core_gt = random.choice(forward_prover.get_equality_ground_truth()) # ground truth 是一堆LogicStatement, 在initialize的时候就只有每一个entity等于自身
            if not problem_graph.is_node_in_graph(core_gt): # 说明该gt还没有被用过，which means是一个root节点
                new_node = ProofNode(step_dict={"lemma": None, 'logic_statement': core_gt, 'operands': []}, lemma_type=None)
                problem_graph.add_node(new_node)
        elif lemma.input_type == 'inequality':
            core_gt = sample_ls(problem_graph, forward_prover.get_fuzzy_inequality_ground_truth(), 0.9)
            # core_gt = random.choice(forward_prover.get_fuzzy_inequality_ground_truth())
            if not problem_graph.is_node_in_graph(core_gt): # 说明该gt还没有被用过，which means是一个root节点
                new_node = ProofNode(step_dict={"lemma": None, 'logic_statement': core_gt, 'operands': []}, lemma_type=None)
                problem_graph.add_node(new_node)
        elif lemma.input_type == 'mixed':
            core_gt = sample_ls(problem_graph, forward_prover.get_fuzzy_inequality_ground_truth() + \
                                    forward_prover.get_equality_ground_truth(), 0.9)
            if not problem_graph.is_node_in_graph(core_gt): # 说明该gt还没有被用过，which means是一个root节点
                new_node = ProofNode(step_dict={"lemma": None, 'logic_statement': core_gt, 'operands': []}, lemma_type=None)
                problem_graph.add_node(new_node)
        elif lemma.input_type == 'theorem':
            core_gts = forward_prover.get_ground_truth()
            # print(f"lemma:{lemma.name}")
            filtered_ls, filtered_ls_status = lemma.construct_ls_with_input_constraints(core_gts, entities, check_solver)
            if filtered_ls == None:
                continue
            for idx, status in enumerate(filtered_ls_status):
                new_ls = filtered_ls[idx]
                if status:
                    forward_prover.condition_ids.extend([forward_prover.add_logic_statement(new_ls)])
                    forward_prover.update_conditions()
                    premise_names.append(new_ls.name)
                # 要么是新构造的，要么是已有在graph里的，要么是一直在gt里但是没被用过的
                new_node = ProofNode(step_dict={"lemma": None, 'logic_statement': new_ls, 'operands': []}, lemma_type=None)
                problem_graph.add_node(new_node)
        else:
            raise NotImplementedError
        
        if lemma.lemma_type == 'axiom' or lemma.lemma_type == 'ordered_axiom':
            # 我感觉是lemma application是看看这个lemma能不能用
            len_steps_before = len(steps)
            if lemma.lemma_type == 'axiom' and lemma.input_type == 'mixed' and \
                (core_gt.logic_function.name == "BiggerOrEqual" or core_gt.logic_function.name == "SmallerOrEqual"):
                lemma_application = apply_ordinary_lemma(
                    0, True, forward_prover, lemma, core_gt, entities,
                    transformed_solutions, premise_names, no_atom_ent, steps, check_solver)
            else:
                lemma_application = apply_ordinary_lemma(
                    probability_no_transform, transform_gt, forward_prover, lemma, core_gt, entities,
                    transformed_solutions, premise_names, no_atom_ent, steps, check_solver)
            len_steps_after = len(steps)
            
            # The problem is too large in some aspects, abandon this generation
            if lemma_application == None:
                continue
            
            result, new_core_gt, how_to_extend, make_up_conclusions = lemma_application
            
            if result != None and new_core_gt != False and len_steps_after != len_steps_before:
                parents_nodes = [core_gt]
                latest_step = steps[-1]
                assumption_ids, conclusion_ids = result["assumption_ids"], result["conclusion_ids"]
                assumps_ls = [forward_prover.ls_id2ls[assump] for assump in assumption_ids]
                conclusion_ls = [forward_prover.ls_id2ls[conc_id] for conc_id in conclusion_ids]
                if len(make_up_conclusions) > 0 or len(assumption_ids) > 0:
                    for make_con in make_up_conclusions+assumps_ls:
                        make_up_con_node = ProofNode(step_dict={"lemma": None, 'logic_statement': make_con, 'operands': []}, lemma_type=None)
                        problem_graph.add_node(make_up_con_node)
                        parents_nodes.append(make_up_con_node)
                for conc in conclusion_ls:
                    new_node = ProofNode(step_dict={"lemma":lemma, 'logic_statement': conc, 'operands': latest_step['input_entities'], 'step':latest_step},
                                    lemma_type=lemma.lemma_type)
                    problem_graph.add_node(new_node, parents_nodes)
            
                # Apply substitution
                # substitution是看看lemma如何具体应用上去,也就是做变量替代,在generate定理的时候, 应用等式的时候做变量替代
                substitution_application = \
                    apply_substitution(forward_prover, steps, result, how_to_extend, make_up_conclusions)
                
                if substitution_application is None:
                    print('bug')
                    substitution_application = \
                        apply_substitution(forward_prover, steps, result, how_to_extend, make_up_conclusions)
                    return
                
                if not substitution_application[0]:
                    continue
                
                len_steps_sub = len(steps)
                assert len_steps_sub != len_steps_after
                latest_step = steps[-1]
                parents_nodes = []
                parent_ls = forward_prover.ls_id2ls[result["conclusion_ids"][0]]
                _, sub_result = substitution_application
                assumption_ids, conclusion_ids = sub_result["assumption_ids"], sub_result["conclusion_ids"]
                assumps_ls = [forward_prover.ls_id2ls[assump] for assump in assumption_ids]
                conclusion_ls = [forward_prover.ls_id2ls[conc_id] for conc_id in conclusion_ids]
                if len(assumption_ids) > 0:
                    for make_con in assumps_ls:
                        make_up_con_node = ProofNode(step_dict={"lemma": None, 'logic_statement': make_con, 'operands': []}, lemma_type=None)
                        problem_graph.add_node(make_up_con_node)
                        parents_nodes.append(make_up_con_node)
                for conc in conclusion_ls:
                    new_node = ProofNode(step_dict={"lemma":all_axioms["EquivalenceSubstitution"], 'logic_statement':conc, 'operands':latest_step['input_entities'], 'step':latest_step},
                                    lemma_type='axiom')
                    problem_graph.add_node(new_node, parents_nodes)
                
                
        elif lemma.lemma_type == 'theorem':
            # print(f"prover.conditions:{forward_prover.get_ground_truth()}")
            # print(f"filtered_ls:{filtered_ls}")
            # print(f"lemma:{lemma.name}")
            operands = lemma.get_operands_from_valid_ls(filtered_ls, entities)
            result = forward_prover.apply_theorem(lemma, operands)
            assumption_ids, conclusion_ids = result["assumption_ids"], result["conclusion_ids"]
            assumps_ls = [forward_prover.ls_id2ls[assump] for assump in assumption_ids]
            conclusion_ls = [forward_prover.ls_id2ls[conc_id] for conc_id in conclusion_ids]
            
            if len(assumption_ids) > 0:
                for assump_ls in assumps_ls:
                    # print(f"assump_ls:{assump_ls}")
                    # print(f"problem_graph:{[node.name for node in problem_graph.nodes]}")
                    assert problem_graph.is_node_in_graph(assump_ls)
            
            for conc in conclusion_ls:
                new_node = ProofNode(step_dict={"lemma":lemma, 'logic_statement': conc, 'operands':operands},
                                lemma_type=lemma.lemma_type)
                problem_graph.add_node(new_node, filtered_ls)
        if no_atom_ent > no_atom_ent_max or len(forward_prover.ent_id2ent) > no_node_max:
            # print(f"too large: {no_atom_ent}, {len(forward_prover.ent_id2ent)}, {lemma_application}")
            return
    
    # Add made up premises and delete redundant trivial premises
    leaf_nodes = problem_graph.get_leaf_nodes()
    leaf_nodes = list(filter(lambda node: node.get_ls_length() < 512, leaf_nodes))
    if len(leaf_nodes) == 0:
        return None, None, None
    chosen_node = None
    cur_length = 0
    for leaf_node in leaf_nodes:
        if leaf_node.ancesters_num >= cur_length:
            chosen_node = leaf_node
            cur_length = leaf_node.ancesters_num
    
    compact_proof_graph = problem_graph.compact_proof_graph(chosen_node)
    root_nodes = compact_proof_graph.get_root_nodes()
    conditions = []
    objectives = [chosen_node._logic_statement]
    for root_node in root_nodes:
        if root_node._logic_statement.operands[0].name != root_node._logic_statement.operands[1].name and \
            not is_all_operands_constant(root_node._logic_statement):
            conditions.append(root_node._logic_statement)
    # problem_graph.visualize()
    # print(f"leaf_node:{chosen_node.ancesters_num}")
    return conditions, objectives, compact_proof_graph

def multi_path_generate_problem(num_axioms, train_test, **kwargs):
    """
    Generate one single theorem and its proof according to requirements
    Return the proof steps, from which the theorem can be easily extracted
    """
    # time_start = time.time()

    avoid_objective_names = kwargs.get("avoid_objective_names", [])
    length = kwargs.get("length", None)
    if length is None:
        length = 0
    # Get combos or orders ready
    # 对于默认给定的脚本，use_orders是true，use_combos是false，k_combos是none，kl_orders是从json里面把对应的k-l的orders给取出来了
    # available_indices似乎是把90%的orders对应的index给取出来了, which is [0，1，2，3，...]
    use_combos, use_orders, k_combos, k_orders, available_indices = \
        get_combo_order_info(num_axioms, train_test, **kwargs)
    # Initialize the atomic entities and the proof
    # atom_ents是list,里面是一堆Entity, 奥这个其实是一些原子的entity, 比如a, b, c,根据degree相关
    # prover是一个既能prove, 又能generate的东西
    atom_ents, prover = initialize_prover(**kwargs)

    done = False
    returned_steps = None
    while not done:
        # 从所有个order中随机选一个或者是从combo整一个,就是一个axiom构成的list
        axiom_order = randomize_one_axiom_order(use_combos, use_orders, k_combos, k_orders, available_indices)
        if len(axiom_order) < length:
            continue
        result = get_a_forward_problem(atom_ents, prover, axiom_order, **kwargs)
        
        if result is None:
            continue
        
        conditions, objectives, compact_proof_graph = result
        steps = graph_forward_to_backward(compact_proof_graph)
        
        if steps == None or steps == False:
            continue
        
        try:
            # Convert the proof to backward and validate it
            returned_steps = generate_valid_steps(steps)
            if returned_steps == False:
                continue
        except TypeError:
            continue
        
        if returned_steps[0]["observation"]["objectives"][0].name in avoid_objective_names:
            # print('not proof_agrees_with_specs')
            continue
        # compact_proof_graph.visualize()
        done = True
    steps_valid(returned_steps)

    return returned_steps

def test_multi_path_generate_problem(num_axioms, length, train_test, axiom_order, **kwargs):
    """
    Generate one single theorem and its proof according to requirements
    Return the proof steps, from which the theorem can be easily extracted
    """
    # time_start = time.time()

    avoid_objective_names = kwargs.get("avoid_objective_names", [])
    # Get combos or orders ready
    # 对于默认给定的脚本，use_orders是true，use_combos是false，k_combos是none，kl_orders是从json里面把对应的k-l的orders给取出来了
    # available_indices似乎是把90%的orders对应的index给取出来了, which is [0，1，2，3，...]
    
    # use_combos, use_orders, k_combos, kl_orders, available_indices = \
    #     get_combo_order_info(num_axioms, length, train_test, **kwargs)
    
    # Initialize the atomic entities and the proof
    # atom_ents是list,里面是一堆Entity, 奥这个其实是一些原子的entity, 比如a, b, c,根据degree相关
    # prover是一个既能prove, 又能generate的东西
    atom_ents, prover = initialize_prover(**kwargs)

    done = False
    returned_steps = None
    while True:
        while not done:
            # 从所有个order中随机选一个或者是从combo整一个,就是一个axiom构成的list
            # axiom_order = randomize_one_axiom_order(use_combos, use_orders, k_combos, kl_orders, available_indices, length)
            start = time.time()
            result = get_a_forward_problem(atom_ents, prover, axiom_order, **kwargs)
            end = time.time()
            if result != None:
                conditions, objectives, proof_graph = result
                # proof_graph.visualize()
                print(f"conditions={[my_logic_statement_to_seq_string(con) for con in conditions]}")
                print(f"objectives={[my_logic_statement_to_seq_string(obj) for obj in objectives]}")
                print(f"time={end-start}\n")
                
                steps = graph_forward_to_backward(proof_graph)
                if steps == None:
                    continue
                if steps == False:
                    print('steps is False')
                    dd
            else:
                dd

            try:
                # TODO: Temporary fix, need to investigate
                # Convert the proof to backward and validate it
                
                returned_steps = generate_valid_steps(steps)
                if returned_steps == False:
                    continue
            except TypeError:
                print('TypeError')
                # returned_steps = generate_valid_steps(steps)
                # dd
                continue
            if returned_steps[0]["observation"]["objectives"][0].name in avoid_objective_names:
                print('not proof_agrees_with_specs')
                continue
            # done = True
        steps_valid(returned_steps)

    return returned_steps

# 生成num个问题，也就是调用num次generate_problem
def _generate_many_problems(num: int, arg_dict):
    # print(f'generate_many_problems start num={num}')
    # start_time = time.time()
    ans = [multi_path_generate_problem(**arg_dict) for _ in range(num)]
    # print(f'generate_many_problems done num={num} time={time.time() - start_time}')
    return ans

def generate_multiple_problems(num_axioms, max_length, num_probs, **kwargs):
    
    separate_problems = {} # 所有的问题,每一个问题是一个单独的list
    all_steps = {} # 所有的问题的所有的step拼到了一块
    all_first_steps = {} # 所有的问题的第一个step拼到了一块

    num_sub_works = 20
    
    # assert sum(num_problems_per_subprocess) == 5 * num_probs
    if 'length' in kwargs.keys():
        # assert max_length == kwargs['length']
        max_length = kwargs['length']
        assert kwargs['length'] >= 3
        num_problems_per_subprocess = [5 * num_probs // num_sub_works for _ in range(num_sub_works)]
        print('specify problem length')
    else:
        print(f"problem length is not specified, will generate problems less than {max_length}")
        num_problems_per_subprocess = [(max_length//3) * num_probs // num_sub_works for _ in range(num_sub_works)]
    orders = kwargs.get('orders', None)
    if orders != None:
        if 'length' in kwargs.keys():
            tgt_len = int(2.4*kwargs['length']) + 1
            for this_length in reversed(range(tgt_len)):
                if f'k{num_axioms}l{this_length}' in orders.keys():
                    kwargs['orders'] = {f'k{num_axioms}': orders[f'k{num_axioms}l{this_length}']}
                    break
        else:
            tgt_len = int(2.4*max_length) + 1
            for this_length in reversed(range(tgt_len)):
                if f'k{num_axioms}l{this_length}' in orders.keys():
                    kwargs['orders'] = {f'k{num_axioms}': orders[f'k{num_axioms}l{this_length}']}
                    break
    else:
        assert False
    generate_problem_args = dict(num_axioms=num_axioms, **kwargs)
    last_problems_num = 0
    if 'length' not in kwargs.keys(): # 生成小于等于max_length的问题
        with ProcessPoolExecutor(max_workers=20) as executor:
            while True:
                # 这个map函数就是调用generate_many_problems，然后后面两个数组分别是传入的第一个和第二个参数，然后生成一个迭代器
                for generated_steps_arr in executor.map(_generate_many_problems, num_problems_per_subprocess,
                                                        (generate_problem_args for _ in range(num_sub_works))):
                    for generated_steps in generated_steps_arr:
                        if len(generated_steps) > max_length or len(generated_steps) < max(3, max_length//2):
                            continue
                        if f"k={num_axioms}l={max_length}" not in all_steps.keys(): 
                            all_steps[f"k={num_axioms}l={max_length}"] = generated_steps # generated_steps是一个单独的问题
                            all_first_steps[f"k={num_axioms}l={max_length}"] = [generated_steps[0]] # 一个单独的问题的第一个step
                            separate_problems[f"k={num_axioms}l={max_length}"] = [deepcopy(generated_steps)]
                        else:
                            if len(separate_problems[f"k={num_axioms}l={max_length}"]) >= num_probs:
                                continue
                            all_steps[f"k={num_axioms}l={max_length}"].extend(generated_steps) # generated_steps是一个单独的问题
                            all_first_steps[f"k={num_axioms}l={max_length}"].append(generated_steps[0]) # 一个单独的问题的第一个step
                            separate_problems[f"k={num_axioms}l={max_length}"].append(generated_steps)
                last_problems_num = sum([len(sp) for sp in separate_problems.values()])
                print(f"generated {[len(sp) for sp in separate_problems.values()]} problems")
                if last_problems_num < num_probs:
                    continue
                else:
                    break
    else: # specify length of the problems
        with ProcessPoolExecutor(max_workers=20) as executor:
            while True:
                # 这个map函数就是调用generate_many_problems，然后后面两个数组分别是传入的第一个和第二个参数，然后生成一个迭代器
                for generated_steps_arr in executor.map(_generate_many_problems, num_problems_per_subprocess,
                                                        (generate_problem_args for _ in range(num_sub_works))):
                    for generated_steps in generated_steps_arr:
                        if len(generated_steps) != kwargs['length']:
                            continue
                        if f"k={num_axioms}l={len(generated_steps)}" not in all_steps.keys(): 
                            all_steps[f"k={num_axioms}l={len(generated_steps)}"] = generated_steps # generated_steps是一个单独的问题
                            all_first_steps[f"k={num_axioms}l={len(generated_steps)}"] = [generated_steps[0]] # 一个单独的问题的第一个step
                            separate_problems[f"k={num_axioms}l={len(generated_steps)}"] = [deepcopy(generated_steps)]
                        else:
                            if len(separate_problems[f"k={num_axioms}l={len(generated_steps)}"]) >= num_probs:
                                continue
                            all_steps[f"k={num_axioms}l={len(generated_steps)}"].extend(generated_steps) # generated_steps是一个单独的问题
                            all_first_steps[f"k={num_axioms}l={len(generated_steps)}"].append(generated_steps[0]) # 一个单独的问题的第一个step
                            separate_problems[f"k={num_axioms}l={len(generated_steps)}"].append(generated_steps)
                # if sum([len(sp) for sp in separate_problems.values()]) == last_problems_num:
                #     assert False, 'no new problems generated'
                last_problems_num = sum([len(sp) for sp in separate_problems.values()])
                print(f"generated {len(list(separate_problems.values())[0])} problems")
                if last_problems_num < num_probs:
                    continue
                else:
                    break
        
    # print(f"avg proof length:{len(all_steps)/len(separate_problems)}")
    for key, _ in all_steps.items():
        random.shuffle(all_steps[key])
        random.shuffle(all_first_steps[key])
    all_steps_dataset = {}
    all_first_steps_dataset = {}
    for key in all_steps.keys():
        all_steps_dataset[key] = Dataset(all_steps[key])
        all_first_steps_dataset[key] = Dataset(all_first_steps[key])

    multiple_problem_datasets = {
        "all": all_steps_dataset,
        "all_first": all_first_steps_dataset,
    }

    return multiple_problem_datasets, separate_problems

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Mode generator')
    parser.add_argument('--orders_path',
                        default="data/benchmark/ordered_field")
    parser.add_argument('--dump_path', '-dp',
                        default="./problems")
    parser.add_argument('-k', type=int, default=5)
    parser.add_argument('-l', type=int, default=None) # 指定问题的长度
    parser.add_argument('-max_l', type=int, default=None) # 指定问题的最大长度
    parser.add_argument('--degree', type=int, default=0)
    parser.add_argument('--num_probs', type=int, default=100)
    args = parser.parse_args()
    assert (args.l is not None or args.max_l is not None) and not (args.l is not None and args.max_l is not None)
    
    orders = json.load(open(os.path.join(args.orders_path, "orders.json"), "r"))

    global_var._init()
    global_var.set_value('COUNT', 0)
    if args.l is not None:
        kwargs = {'length': args.l}
    else:
        kwargs = {}
    datasets, problems = generate_multiple_problems(num_axioms=args.k, max_length=args.max_l,
                                                    num_probs=args.num_probs, train_test="train",
                                                    orders=orders, degree=args.degree, **kwargs)
    if args.max_l is not None:
        for l in range(args.max_l, args.max_l+1):
            kl_dir = os.path.join(args.dump_path, args.orders_path.split("/")[-1], "k={}_l={}".format(args.k, l))
            if not os.path.isdir(kl_dir):
                os.makedirs(kl_dir)
            key = f"k={args.k}l={l}"
            
            if os.path.isdir(os.path.join(kl_dir, "train")):
                shutil.rmtree(os.path.join(kl_dir, "train"))
            os.mkdir(os.path.join(kl_dir, "train"))
            for i, problem in enumerate(problems[key]):
                pickle.dump(problem, open(os.path.join(kl_dir, "train", "steps_{}.p".format(i + 1)), "wb"))

            pickle.dump(datasets["all"][key], open(os.path.join(kl_dir, "train.pkl"), "wb"))
            pickle.dump(datasets["all_first"][key], open(os.path.join(kl_dir, "train_first.pkl"), "wb"))
    else:
        l = args.l
        kl_dir = os.path.join(args.dump_path, args.orders_path.split("/")[-1], "k={}_l={}".format(args.k, l))
        if not os.path.isdir(kl_dir):
            os.makedirs(kl_dir)
        key = f"k={args.k}l={l}"
        
        if os.path.isdir(os.path.join(kl_dir, "train")):
            shutil.rmtree(os.path.join(kl_dir, "train"))
        os.mkdir(os.path.join(kl_dir, "train"))
        for i, problem in enumerate(problems[key]):
            pickle.dump(problem, open(os.path.join(kl_dir, "train", "steps_{}.p".format(i + 1)), "wb"))

        pickle.dump(datasets["all"][key], open(os.path.join(kl_dir, "train.pkl"), "wb"))
        pickle.dump(datasets["all_first"][key], open(os.path.join(kl_dir, "train_first.pkl"), "wb"))
    
    # analyze the statistics of the generated problems
    if args.l is None:
        for l in range(args.max_l, args.max_l+1):
            key = f"k={args.k}l={l}"
            inequ_num = 0
            equ_num = 0 
            extracted_first_steps = [steps[0]["observation"]["objectives"][0] for steps in problems[key]]
            for first_step in extracted_first_steps:
                if first_step.logic_function.name == 'Equivalent':
                    equ_num += 1
                elif first_step.logic_function.name == 'BiggerOrEqual' or \
                    first_step.logic_function.name == 'Bigger' or \
                    first_step.logic_function.name == 'SmallerOrEqual' or \
                    first_step.logic_function.name == 'Smaller':
                    inequ_num += 1
                else:
                    assert False
            for sp in problems[key]:
                print(len(sp))
            print(f"l={l} inequ_num={inequ_num} equ_num={equ_num}")
    
# with ProcessPoolExecutor(max_workers=20) as executor:
        #     while True:
        #         # 这个map函数就是调用generate_many_problems，然后后面两个数组分别是传入的第一个和第二个参数，然后生成一个迭代器
        #         for generated_steps_arr in executor.map(_generate_many_problems, num_problems_per_subprocess,
        #                                                 (generate_problem_args for _ in range(num_sub_works))):
        #             for generated_steps in generated_steps_arr:
        #                 if len(generated_steps) > max_length or len(generated_steps) < 3:
        #                     continue
        #                 if f"k={num_axioms}l={len(generated_steps)}" not in all_steps.keys(): 
        #                     all_steps[f"k={num_axioms}l={len(generated_steps)}"] = generated_steps # generated_steps是一个单独的问题
        #                     all_first_steps[f"k={num_axioms}l={len(generated_steps)}"] = [generated_steps[0]] # 一个单独的问题的第一个step
        #                     separate_problems[f"k={num_axioms}l={len(generated_steps)}"] = [deepcopy(generated_steps)]
        #                 else:
        #                     if len(separate_problems[f"k={num_axioms}l={len(generated_steps)}"]) >= num_probs:
        #                         continue
        #                     all_steps[f"k={num_axioms}l={len(generated_steps)}"].extend(generated_steps) # generated_steps是一个单独的问题
        #                     all_first_steps[f"k={num_axioms}l={len(generated_steps)}"].append(generated_steps[0]) # 一个单独的问题的第一个step
        #                     separate_problems[f"k={num_axioms}l={len(generated_steps)}"].append(generated_steps)
        #         # if sum([len(sp) for sp in separate_problems.values()]) == last_problems_num:
        #         #     assert False, 'no new problems generated'
        #         last_problems_num = sum([len(sp) for sp in separate_problems.values()])
        #         print(f"generated {[len(sp) for sp in separate_problems.values()]} problems")
        #         if last_problems_num < num_probs * (max_length - 2):
        #             continue
        #         else:
        #             break