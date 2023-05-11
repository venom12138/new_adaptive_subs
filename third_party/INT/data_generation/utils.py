import random
from copy import deepcopy
from operator import itemgetter
from collections import OrderedDict
import numpy as np

from torch.utils import data as data_handler

from proof_system.prover import Prover
from proof_system.all_axioms import all_axioms_to_prove, generation_type, all_axioms
from proof_system.logic_functions import necessary_logic_functions
from proof_system.numerical_functions import necessary_numerical_functions, numpy_numerical_functions
from proof_system.utils import is_ls, is_empty_ls, is_entity
from logic.logic import Entity

# 引入N_positive, 可以直接生成一些正数的entity
def generate_starting_ents(degree=0, N_positive=3):
    a = Entity("a", is_iv=True, sign=[1]) 
    b = Entity("b", is_iv=True, sign=[1]) 
    c = Entity("c", is_iv=True, sign=[1]) 
    independent_variables = []
    if N_positive > 0:
        positive_nums = list(np.random.randint(low=1, high=10, size=N_positive)) # 这一阶段禁止有0出现就没问题了
        for num in positive_nums:
            exec(f"entity_{str(int(num))} = Entity('{str(int(num))}', is_constant=True, sign=[1])")
            independent_variables.append(eval(f"entity_{str(int(num))}"))
    
    independent_variables.extend([a, b, c])
    positive_ents_names = [ent.name for ent in independent_variables]
    negative_ents_names = []
    unsigned_ents_names = []
    # degree是0, 所以就是abc，如果degree更高的话，就会有更多的组合
    ent_dict, positive_ents_names, negative_ents_names, unsigned_ents_names = \
        all_entities_to_a_degree(
            atoms=independent_variables,
            operators=necessary_numerical_functions.values(),
            degree=degree,
            positive_ents_names=positive_ents_names,
            negative_ents_names=negative_ents_names,
            unsigned_ents_names=unsigned_ents_names
        )
    return independent_variables, ent_dict, positive_ents_names, negative_ents_names, unsigned_ents_names


def all_entities_to_a_degree(atoms, operators, degree, positive_ents_names, negative_ents_names, unsigned_ents_names):
    """Generate entities up to a certain degree."""
    binary_operators = [operator for operator in operators if operator.input_no == 2]
    singular_operators = [operator for operator in operators if operator.input_no == 1]
    entities = OrderedDict()
    entities[0] = [atom for atom in atoms]
    for d in range(1, 1 + degree):
        entities[d] = list()
        # Binary operators
        for d1 in range(0, d):
            d2 = d - 1 - d1
            for entity1 in entities[d1]:
                for entity2 in entities[d2]:
                    if entity1.is_constant and entity2.is_constant:
                        continue
                    for operator in binary_operators:
                        copied_entity1, copied_entity2 = entity1, entity2
                        result = operator.execute_nf([copied_entity1, copied_entity2])
                        return_value = deduce_the_sign_of_entity(result, positive_ents_names, negative_ents_names, unsigned_ents_names)
                        if return_value == None:
                            continue
                        else:
                            positive_ents_names, negative_ents_names, unsigned_ents_names = \
                                return_value
                        entities[d].append(result)

        # Singular operators
        for entity in entities[d - 1]:
            for operator in singular_operators:
                copied_entity = entity
                result = operator.execute_nf([copied_entity])
                return_value = deduce_the_sign_of_entity(result, positive_ents_names, negative_ents_names, unsigned_ents_names)
                if return_value == None:
                    continue
                else:
                    positive_ents_names, negative_ents_names, unsigned_ents_names = \
                        return_value
                entities[d].append(result)
    return entities, positive_ents_names, negative_ents_names, unsigned_ents_names

# given a entity and a list of positive entities, negative entities
# return the sign of each entity
def deduce_the_sign_of_entity(entity, positive_ents_names, negative_ents_names, unsigned_ents_names):
    entity_copied = deepcopy(entity)
    entity_copied.index = 0
    entity_copied.parent_index = -1
    index = 1
    available_entity_list = [entity_copied]
    id2ent = OrderedDict()
    # index each entity
    while len(available_entity_list) > 0:
        curr_ent = available_entity_list.pop(0)
        id2ent.update({curr_ent.index: curr_ent})
        child_ents = curr_ent.operands
        if child_ents == None:
            if curr_ent.name in positive_ents_names:
                curr_ent.sign = [1]
            elif curr_ent.name in negative_ents_names:
                curr_ent.sign = [-1]
            elif curr_ent.name in unsigned_ents_names:
                curr_ent.sign = [1,-1]
            else:
                raise AssertionError()
        else:
            for child_ent in child_ents:
                child_ent.index = index
                index += 1
                child_ent.parent_index = curr_ent.index
                available_entity_list.append(child_ent)
    deduce_entity_list = []
    for ent in id2ent.values():
        if ent.name in positive_ents_names:
            ent.sign = [1]
        elif ent.name in negative_ents_names:
            ent.sign = [-1]
        elif ent.name in unsigned_ents_names:
            ent.sign = [1,-1]
        else:
            deduce_entity_list.append(ent)
    deduce_entity_list = list(reversed(deduce_entity_list))
    last_deduce_length = len(deduce_entity_list)
    # deduce the sign of each entity
    while len(deduce_entity_list) > 0:
        for ent in deduce_entity_list:
            child_ents = ent.operands
            assert child_ents != None
            assert ent.recent_numerical_function != None
            info = check_entity_sign(ent.recent_numerical_function, child_ents)
            if info == "positive":
                ent.sign = [1]
                positive_ents_names.append(ent.name)
                deduce_entity_list.remove(ent)
            elif info == "negative":
                ent.sign = [-1]
                negative_ents_names.append(ent.name)
                deduce_entity_list.remove(ent)
            elif info == "unsigned":
                ent.sign = [1, -1]
                unsigned_ents_names.append(ent.name)
                deduce_entity_list.remove(ent)
            elif info == "illegal":
                return None
            elif info == None:
                continue
        if len(deduce_entity_list) == last_deduce_length:
            return None
        last_deduce_length = len(deduce_entity_list)
    
    return positive_ents_names, negative_ents_names, unsigned_ents_names

# 用于判断一个operands的sign已经确定了的entity的符号
# return type: None, positive, negative, illegal, unsigned
def check_entity_sign(recent_numerical_function, operands):
    for operand in operands:
        if operand.sign == None:
            return None
    # 特判log，不需要特判pow，这里直接会不允许负数的正数次方，因为在下面会出现nan
    if recent_numerical_function.name == "log":
        operand1, = operands
        if operand1.is_constant:
            if int(operand1.name) <= 0:
                return "illegal"
            elif int(operand1.name) < 1:
                return "negative"
            else:
                return "positive"
        else:
            if operand1.sign == [1]:
                return "unsigned"
            else:
                return "illegal"
    elif recent_numerical_function.name == "pow":
        operand1, operand2 = operands
        if operand1.is_constant and operand2.is_constant:
            numerical_operand1 = float(int(operand1.name))
            numerical_operand2 = float(int(operand2.name))
            result = numpy_numerical_functions[recent_numerical_function.name](numerical_operand1, numerical_operand2)
            if result > 100000:
                return "illegal"
            if np.isnan(result):
                return "illegal"
            elif result < 0:
                return "negative"
            elif result > 0:
                return "positive"
            else:
                return "illegal"
        else:
            if operand1.sign != [1]: # 要求pow只能用这个正数的正负次方
                return "illegal"
        
    if recent_numerical_function.input_no == 1:
        operand1, = operands
        result = []
        for sign in operand1.sign:
            result.append(numpy_numerical_functions[recent_numerical_function.name](float(sign)))
    elif recent_numerical_function.input_no == 2:
        operand1, operand2 = operands
        result = []
        if operand1.name == operand2.name: # 如果是同名的entity，那符号判定就不一样
            assert operand1.sign == operand2.sign
            for i in range(len(operand1.sign)):
                result.append(numpy_numerical_functions[recent_numerical_function.name](float(operand1.sign[i]), float(operand2.sign[i])))
        else:
            for sign1 in operand1.sign:
                for sign2 in operand2.sign:
                    result.append(numpy_numerical_functions[recent_numerical_function.name](float(sign1), float(sign2)))
    is_positive = all(i > 0 for i in result)
    is_negative = all(i < 0 for i in result)
    is_illegal = any(np.isnan(i) for i in result)
    if is_positive:
        return "positive"
    elif is_negative:
        return "negative"
    elif is_illegal:
        return "illegal"
    else:
        return "unsigned"

# 如果能合并的话， 合并几个constant的操作数, 暂时不考虑任何合并的情况，因为可能会产生0, 而且会需要改变entity的name，导致一些很奇怪的情况发生
# def combine_constant_operands(entity):
#     if entity.recent_numerical_function == None:
#         return entity, False
#     assert entity.operands != None
#     opes = entity.operands
#     for ope in opes:
#         if ope.is_constant == False:
#             return entity, False
#     # 能到这说明一定是constant了
#     result = np.around(numpy_numerical_functions[entity.recent_numerical_function.name](*[float(ope.name) for ope in opes]), 3)
#     entity.name = str(result)
#     entity.is_constant = True
    

def steps_valid(steps):
    test_steps = deepcopy(steps)
    if len(test_steps) == 0:
        return "Empty"
    test_proof = Prover(axioms=all_axioms_to_prove,
                        conditions=test_steps[0]["observation"]["ground_truth"],
                        objectives=test_steps[0]["observation"]["objectives"],
                        prove_direction="backward")
    assert not test_proof.is_proved()
    for step in test_steps:
        for k, op in enumerate(step["input_entities"]):
            # Make sure the root of each operand is in the current graphs
            if is_entity(op):
                assert op.root is not None
                assert op.root.name in [ls.name for ls in test_proof.get_ground_truth() +
                                        test_proof.get_objectives()]
                assert op.root in [ls for ls in step["observation"]["ground_truth"] +
                                    step["observation"]["objectives"]]
            elif is_ls(op):
                assert op.name in [ls.name for ls in test_proof.get_ground_truth() +
                                    test_proof.get_objectives()]
                assert op in [ls for ls in step["observation"]["ground_truth"] +
                                step["observation"]["objectives"]]
            else:
                raise AssertionError("Not allowed type: {}".format(type(op)))
        if step["lemma"].name == "EquivalenceSubstitution":
            op1, op2 = step["input_entities"]

            assembled_operands = list()
            available_ents = []
            for ls in test_proof.get_objectives() + test_proof.get_ground_truth():
                available_ents.extend([ls.ent_dic[key] for key in ls.ent_dic if key != 0])

            replacement1 = test_proof.ls_id2ls[test_proof.ls_name2id[op1.root.name]].ent_dic[op1.index]
            assembled_operands.append(replacement1)
            replacement2 = test_proof.ls_id2ls[test_proof.ls_name2id[op2.root.name]].ent_dic[op2.index]
            assembled_operands.append(replacement2)

        else:
            assembled_operands = list()
            for op in step["input_entities"]:
                for ls in test_proof.get_objectives() + test_proof.get_ground_truth():
                    if is_entity(op) and ls.name == op.root.name:
                        assembled_operands.append(ls.ent_dic[op.index])
                        break
                    elif is_ls(op) and ls.name == op.name:
                        assembled_operands.append(ls)
                        break
            assert len(assembled_operands) == step["lemma"].input_no

        test_proof.apply_theorem(theorem=step["lemma"], operands=assembled_operands, )
    # Make sure the proof is complete when all test_steps are carried out
    assert test_proof.is_proved()


def generate_valid_steps(steps):
    valid_steps = list()
    if steps is None or len(steps) == 0:
        return steps
    test_proof = Prover(axioms=all_axioms_to_prove,
                        conditions=steps[0]["observation"]["ground_truth"],
                        objectives=steps[0]["observation"]["objectives"],
                        prove_direction="backward")
    assert not test_proof.is_proved()
    for step in steps:
        if test_proof.is_proved():
            break
        for op in step["input_entities"]:
            assert (is_entity(op) and op.root is not None) or is_ls(op) or is_empty_ls(op)   
            if not (is_entity(op) and op.root.name in
                    [ls.name for ls in test_proof.get_ground_truth() + test_proof.get_objectives()]) or \
                    (is_ls(op) and op.name in
                    [ls.name for ls in test_proof.get_ground_truth() + test_proof.get_objectives()] or
                    is_empty_ls(op)):
                return False

        assert step["lemma"].name != "EquivalenceSubstitution"
        assembled_operands = list()
        for op in step["input_entities"]:
            for ls in test_proof.get_objectives() + test_proof.get_ground_truth():
                if is_entity(op) and ls.name == op.root.name:
                    ls_ent_name_list = [ent.name for ent in ls.ent]
                    op_in_ls = ls.ent[ls_ent_name_list.index(op.name)]
                    assembled_operands.append(op_in_ls) # 这两个ls就不一样，所以咋可能索引的到呢 ls.ent_dic[op.index]
                    # assembled_operands.append(1)
                    break
                elif (is_empty_ls(op) or is_ls(op)) and ls.name == op.name:
                    assembled_operands.append(ls)
                    # assembled_operands.append(1)
                    break
        
        assert len(assembled_operands) == step["lemma"].input_no

        lemma = step["lemma"]
        operands = assembled_operands
        cur_observation = test_proof.get_observation()
        test_proof.apply_theorem(theorem=step["lemma"], operands=assembled_operands)
        
        step = {
            "observation": cur_observation,
            "next_objectives": test_proof.get_objectives(),
            "lemma": lemma,
            "input_entities": operands
        }
        valid_steps.append(step)
        

    # Make sure the proof is complete when all steps are carried out
    if not test_proof.is_proved():
        return False
    return valid_steps


class Dataset(data_handler.Dataset):
    def __init__(self, trajectories):
        self.trajectories = trajectories
        self.io_tuples = list()
        for trajectory in trajectories:
            datapoint = (
                trajectory['observation'], trajectory['lemma'],
                trajectory['input_entities'],
            )
            self.io_tuples.append(datapoint)

    def __getitem__(self, index):
        return self.io_tuples[index]

    def __len__(self):
        return len(self.io_tuples)

    def get_multiple(self, indices):
        if len(indices) == 1:
            return self.io_tuples[indices[0]],
        else:
            return itemgetter(*indices)(self.io_tuples)

    def merge(self, another_dataset):
        total_trajectories = self.trajectories + another_dataset.trajectories
        self.__init__(total_trajectories)

# valid_combos包括: 等式组合, (等式)+转换+不等式组合
def valid_combo(combo_names):
    combo_types = [generation_type[name] for name in combo_names]
    equality = 0
    inequality = 0
    transition = 0
    for combo_type in combo_types:
        if combo_type == "Equality":
            equality += 1
        elif combo_type == "Inequality":
            inequality += 1
        elif combo_type == "Transition":
            transition += 1
        else:
            raise NotImplementedError

    if transition > 1:
        return False
    # 也就是说是从等式开始, 想要应用不等式,必须要先将等式用Transition转化成不等式的组合, 然后才能应用不等式
    # Transition就两个,分别是SquareGEQZero, EquivalenceImpliesDoubleInequality
    # 也就是说INT的逻辑其实是, 不等式应用于不等式,等式应用于等式, 中间通过Transition衔接
    elif transition == 0 and inequality > 0:
        return False
    else:
        return True


def make_up_condition(requirement_type, a, b, no_iv, new_iv=True):
    if new_iv:
        # 这个好像是为了防止重名，搞一个+ no_iv
        c = Entity(name=chr(ord('c') + no_iv), is_iv=True) 
        no_iv += 1
        a_copied = deepcopy(a)
        b_copied = deepcopy(b)
        c_copied = deepcopy(c)
        
        a_plus_c = necessary_numerical_functions["add"].execute_nf([a_copied, c_copied])
        new_conclusion = necessary_logic_functions[requirement_type].execute_lf([a_plus_c, b_copied])
    else:
        a_copied, b_copied = deepcopy(a), deepcopy(b)
        new_conclusion = necessary_logic_functions[requirement_type].execute_lf([a_copied, b_copied])

    return {
        "conclusion": new_conclusion,
        "no_iv": no_iv
    }


def find_entity_with_name(ls, target_name):
    for ent_id, ent in ls.ent_dic.items():
        if ent.name == target_name:
            return ent
    raise AssertionError


def proof_agrees_with_specs(backward_steps, length, axiom_order, avoid_objective_names):
    if backward_steps is None or len(backward_steps) != length or \
            set([step["lemma"].name for step in backward_steps]) != set(axiom_order) or \
            backward_steps[0]["observation"]["objectives"][0].name in avoid_objective_names:
        return False
    return True


def initialize_prover(ivs=None, ed=None, ent_per_degree=10, degree=0, **kwargs):
    # Initialize the starting entities and the proof
    if ivs is None and ed is None:
        # 给定脚本中，是none，需要生成
        ivs, ed, positive_ents_names, negative_ents_names, unsigned_ents_names = generate_starting_ents(degree=degree)
        # ivs是list,里面是一堆Entity, 也就是独立变量
        # ed是OrderedDict,里面是 {k:Entity的list}，其中k是degree，list是对应degree的entity的组合，他的字典的key是1到1+degree
    starting_ents = list()
    # starting就是随机sample一些entity的组合，太合理了
    for k in sorted(ed.keys()):
        starting_ents.extend(random.sample(ed[k], k=min(ent_per_degree, len(ed[k]))))
    random.shuffle(starting_ents)
    ground_truth = list()
    zero_entity = Entity(name="0", is_constant=True) # 要求每一个individual的entity都大于0, 而不是starting_entities，因为starting_entities是随机的
    for ent in starting_ents:
        # 嗷,这个groundtruth是说, 任意一个entity都和自己等价，这也是最初的gt
        if ent.name in positive_ents_names:
            ground_truth.append(necessary_logic_functions["BiggerOrEqual"].execute_lf([ent, zero_entity]))
        elif ent.name in negative_ents_names:
            ground_truth.append(necessary_logic_functions["SmallerOrEqual"].execute_lf([ent, zero_entity]))
        ground_truth.append(necessary_logic_functions["Equivalent"].execute_lf([ent, ent])) # 这玩意返回的是一个LogicStatement,也不知道有啥用
    for iv in ivs:
        ground_truth.append(necessary_logic_functions["BiggerOrEqual"].execute_lf([ent, zero_entity])) 
    prover = Prover(axioms=all_axioms, conditions=ground_truth, objectives=[], prove_direction="forward") # 生成一个既能prove, 又能generate的东西
    return ivs, prover

# 这个函数就是拿出所有的gt，每个gt是一个logic_statement, 
# 把每一个ls的那棵树拿出来，再把树中所有是entity的node拿出来
def gather_available_entities(proof, entity_length_limit):
    # Gather available entities from premises and proven facts
    entities = list()
    entity_names = set()
    for gt in proof.get_ground_truth():
        # ent_dic就是那个证明树，这个字典是按照树中每个节点的id来组织的
        for key in sorted(gt.ent_dic.keys()):
            # 这里的value是Equivalent(a, a),a这种东西
            # 由于只要gather entities,所以最后只有a,b,c这样子的被返回回去
            value = gt.ent_dic[key]
            
            if isinstance(value, Entity) and value.name not in entity_names \
                    and len(value.name) <= entity_length_limit:
                entities.append(value)
                entity_names.add(value.name)
    return entities
