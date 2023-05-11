from proof_system.prover import Prover
from proof_system.all_axioms import all_axioms_to_prove
from proof_system.utils import EmptyLogicStatement, get_entity_from_ls_and_coding, \
    get_entity_coding_from_ls, is_entity, all_different_subtrees
from data_generation.utils import find_entity_with_name
from proof_system.special_axioms import EquivalenceSubstitution
from proof_system.utils import is_ls_type, is_all_operands_constant, numerical_compute_logic_statement
import random
random.seed(0)

def generate_steps_from_graph(proof_graph):
    leaf_nodes = proof_graph.get_leaf_nodes()
    assert len(leaf_nodes) == 1
    leaf_node = leaf_nodes[0]
    node_idx_list = [leaf_node.index] # temporal list
    node_idx_stack = [leaf_node.index] # return stack
    if leaf_node.lemma.name == 'EquivalenceSubstitution':
        assert len(leaf_node.parents_idxs) == 2
        if leaf_node.parents_idxs[0] in proof_graph.nd_id2node[leaf_node.parents_idxs[1]].parents_idxs:
            assert leaf_node.parents_idxs[1] not in node_idx_stack
            node_idx_list.append(leaf_node.parents_idxs[1])
            node_idx_stack.append(leaf_node.parents_idxs[1])
        elif leaf_node.parents_idxs[1] in proof_graph.nd_id2node[leaf_node.parents_idxs[0]].parents_idxs:
            assert leaf_node.parents_idxs[0] not in node_idx_stack
            node_idx_list.append(leaf_node.parents_idxs[0])
            node_idx_stack.append(leaf_node.parents_idxs[0])
        else:
            raise NotImplementedError
    
    while len(node_idx_list) > 0:
        cur_node_idx = node_idx_list.pop(0)
        cur_node = proof_graph.nd_id2node[cur_node_idx]
        if len(cur_node.parents_idxs) > 0:
            for p_idx in cur_node.parents_idxs:
                if p_idx not in node_idx_stack and len(proof_graph.nd_id2node[p_idx].parents_idxs) > 0:
                    node_idx_list.append(p_idx)
                    node_idx_stack.append(p_idx)
                    if proof_graph.nd_id2node[p_idx].lemma.name == 'EquivalenceSubstitution':
                        assert len(proof_graph.nd_id2node[p_idx].parents_idxs) == 2
                        if proof_graph.nd_id2node[p_idx].parents_idxs[0] in proof_graph.nd_id2node[proof_graph.nd_id2node[p_idx].parents_idxs[1]].parents_idxs:
                            if proof_graph.nd_id2node[p_idx].parents_idxs[1] in node_idx_stack:
                                node_idx_stack.remove(proof_graph.nd_id2node[p_idx].parents_idxs[1])
                            node_idx_list.append(proof_graph.nd_id2node[p_idx].parents_idxs[1])
                            node_idx_stack.append(proof_graph.nd_id2node[p_idx].parents_idxs[1])
                        elif proof_graph.nd_id2node[p_idx].parents_idxs[1] in proof_graph.nd_id2node[proof_graph.nd_id2node[p_idx].parents_idxs[0]].parents_idxs:
                            if proof_graph.nd_id2node[p_idx].parents_idxs[0] in node_idx_stack:
                                node_idx_stack.remove(proof_graph.nd_id2node[p_idx].parents_idxs[0])
                            node_idx_list.append(proof_graph.nd_id2node[p_idx].parents_idxs[0])
                            node_idx_stack.append(proof_graph.nd_id2node[p_idx].parents_idxs[0])
                        else:
                            raise NotImplementedError
                elif p_idx not in node_idx_stack:
                    node_idx_list.append(p_idx)
                    node_idx_stack.append(p_idx)
    
    return [proof_graph.nd_id2node[idx] for idx in node_idx_stack], node_idx_stack


# 我懂这个证明的逻辑了，对于extend_core_gt产生出来的statement来说，他只需要通过original_coding，然后匹配到statement中对应的entity
# 然后就完成了一步证明，对应的entity就作为新的lhs和rhs进入到下一步证明中，不对，其实本质上还是依靠apply_theorem来完成的
def graph_forward_to_backward(proof_graph, unittest=True, debug=False):
    if proof_graph is None or len(proof_graph.nodes) <= 1:
        return None
    
    sorted_nodes, sorted_node_idxs = generate_steps_from_graph(proof_graph)
    condition_nodes = []
    procedural_nodes = []
    for i in range(len(sorted_nodes)):
        cur_node = sorted_nodes[i]
        if len(cur_node.parents_idxs) == 0:
            if cur_node._logic_statement.operands[0].name != cur_node._logic_statement.operands[1].name and \
                not is_all_operands_constant(cur_node._logic_statement):
                condition_nodes.append(cur_node)
        else:
            procedural_nodes.append(cur_node)
    ground_truths = [con_node._logic_statement for con_node in condition_nodes]
    objectives = [procedural_nodes[0]._logic_statement]
    
    proof = Prover(
        axioms=all_axioms_to_prove,
        conditions=ground_truths, # 这个是steps[0]的ground_truth，也就是说，后面产生的新的ground_truth都没有被加入进来，只有make_up_conditions，我需要把一些一开始的condition给罗列进去
        objectives=objectives,
        prove_direction="backward"
    )

    if proof.is_proved():
        return None
    hypo_objective = proof.get_objectives()[0]
    translated_steps = list()
    iteration = 0
    # print('forward_to_backward')
    while len(procedural_nodes) > 0 and (not proof.is_proved()):
        iteration += 1
        if iteration >= 30:
            return None
        step = None
        step_node = procedural_nodes.pop(0) # 移除第一个元素
        
        if step_node.lemma.name == "EquivalenceSubstitution": # 这个好像是说，如果是EquivalenceSubstitution，那么就直接跳到下一步，也不是
            last_step_node = procedural_nodes.pop(0)
            last_step = last_step_node.step
            step = step_node.step
            assert last_step["lemma"].name != "EquivalenceSubstitution"
            transform_gt = last_step["transform_gt"]
            if transform_gt: # 这个
                transformed_side = last_step["transformed_side"]
                lemma = last_step["lemma"]
                if lemma.input_no == 1:
                    coding = get_entity_coding_from_ls(step["input_entities"][0].root, step["input_entities"][0]) # 这里相当于是确定了hypo_objective和input_entities.root是同一个东西，这也就意味着在这一套逻辑里，是不会存在多个证明的分支的
                    operand = get_entity_from_ls_and_coding(hypo_objective, coding)
                    operands = [operand]
                else:
                    first_op_name = lemma.transform_recover_first_name(step["input_entities"]) # input_no=2的情况不多见
                    found_first_name = False
                    for ls in proof.get_objectives() + proof.get_ground_truth():
                        if (len(first_op_name) == 1 and first_op_name in ls.name.split()) or \
                                (len(first_op_name) != 1 and first_op_name in ls.name):
                            found_first_name = True
                            first_op = find_entity_with_name(ls, first_op_name)
                    assert found_first_name

                    coding = get_entity_coding_from_ls(step["input_entities"][1].root, step["input_entities"][1])
                    second_op = get_entity_from_ls_and_coding(hypo_objective, coding)
                    operands = [first_op, second_op]

            else:
                lemma = last_step["lemma"]
                operands = last_step["lemma"].prove_operands(hypo_objective)
                coding = last_step["original_coding"]

            step = last_step
            
        elif step_node.lemma_type == 'axiom' or step_node.lemma_type == 'ordered_axiom':
            step = step_node.step
            lemma = step["lemma"]
            operands = step["lemma"].prove_operands(hypo_objective)
            coding = step["original_coding"]
            transform_gt = step["transform_gt"]
            if transform_gt:
                transformed_side = step["transformed_side"]

        elif step_node.lemma_type == 'theorem':
            operands = step_node._logic_statement.operands
            lemma = step_node.lemma
            transform_gt = False
            coding = None
            
        cur_observation = proof.get_observation()
        proof.apply_theorem(theorem=lemma,
                            operands=operands, )
        translated_steps.append(
            {
                "observation": cur_observation,
                "next_objectives": proof.get_objectives(),
                "lemma": lemma,
                "input_entities": operands
            }
        )
        if proof.is_proved():
            return translated_steps
                
        if transform_gt: # transform_gt肯定只会对一边进行变换，另一边肯定会保持不变
            all_diff_subtrees = all_different_subtrees(proof.get_objectives()[0]) # 这个其实是进行了一步简化分析，直接把相同的给去掉了，因为相同的肯定就直接相等了，好像不对
            done = False
            while all_diff_subtrees and (not done):
                lhs, rhs = all_diff_subtrees.pop(0)
                if lhs is not None:
                    if transformed_side == "left":
                        hypo_lhs, hypo_rhs, = hypo_objective.operands
                        if hypo_rhs.name == lhs.name:
                            hypo_objective = EmptyLogicStatement(None, [rhs, lhs])
                            done = True
                        elif hypo_rhs.name == rhs.name: # 左边变了，右边没变
                            hypo_objective = EmptyLogicStatement(None, [lhs, rhs])
                            done = True
                        else:
                            pass
                    elif transformed_side == "right":
                        hypo_lhs, hypo_rhs, = hypo_objective.operands
                        if hypo_lhs.name == lhs.name:
                            hypo_objective = EmptyLogicStatement(None, [lhs, rhs])
                            done = True
                        elif hypo_lhs.name == rhs.name:
                            hypo_objective = EmptyLogicStatement(None, [rhs, lhs])
                            done = True
                        else:
                            pass
                    elif transformed_side == "custom":
                        hypo_objective = step["custom_function"](proof.get_objectives()[0], hypo_objective)
                        done = True
                    else:
                        raise NotImplementedError
        elif coding is None: # big change
            while len(procedural_nodes) > 0:
                candidate_node = procedural_nodes[0]
                # try:
                if is_all_operands_constant(candidate_node._logic_statement):
                    if numerical_compute_logic_statement(candidate_node._logic_statement):
                        procedural_nodes.pop(0)
                        continue
                    else:
                        #TODO: 这里会触发bug,很奇怪
                        if not candidate_node._logic_statement.name in [objective.name for objective in proof.get_objectives()]:
                            return False
                else:
                    if not candidate_node._logic_statement.name in [objective.name for objective in proof.get_objectives()]:
                        return False
                        # print('dfdfdfd')
                        # assert candidate_node._logic_statement.name in [objective.name for objective in proof.get_objectives()], candidate_node._logic_statement.name
                for objective in proof.get_objectives():
                    if candidate_node._logic_statement.name == objective.name:
                        hypo_objective = objective
                        break
                break
        else:
            hypo_lhs = get_entity_from_ls_and_coding(hypo_objective, coding[0]) # 确实，需要coding的原因是，需要把这个entity从ls中取出来，不能是随意乱构造一个同名的entity，因为需要entity.root
            hypo_rhs = get_entity_from_ls_and_coding(hypo_objective, coding[1])
            if hypo_lhs is False or hypo_rhs is False:
                return False
            all_diff_subtrees = all_different_subtrees(proof.get_objectives()[0])
            done = False
            while all_diff_subtrees and (not done): # 这个hypo_objective的作用其实是做一步double check，因为这是一个深搜，所以一定存在这样的对应关系
                lhs, rhs = all_diff_subtrees.pop(0)
                if lhs is not None:
                    if lhs.name == hypo_lhs.name and rhs.name == hypo_rhs.name:
                        hypo_objective = EmptyLogicStatement(None, [lhs, rhs])
                        done = True
                    elif lhs.name == hypo_rhs.name and rhs.name == hypo_lhs.name:
                        hypo_objective = EmptyLogicStatement(None, [rhs, lhs])
                        done = True
                    elif is_entity(lhs) and is_entity(rhs):
                        pass
                    else:
                        return False
                    
    if proof.is_proved():
        return translated_steps
    return False
