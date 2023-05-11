from proof_system.prover import Prover
from proof_system.all_axioms import all_axioms_to_prove
from proof_system.utils import EmptyLogicStatement, get_entity_from_ls_and_coding, \
    get_entity_coding_from_ls, is_entity, all_different_subtrees
from data_generation.utils import find_entity_with_name

import random

random.seed(0)

# 我懂这个证明的逻辑了，对于extend_core_gt产生出来的statement来说，他只需要通过original_coding，然后匹配到statement中对应的entity
# 然后就完成了一步证明，对应的entity就作为新的lhs和rhs进入到下一步证明中，不对，其实本质上还是依靠apply_theorem来完成的
def forward_to_backward(steps, unittest=True, debug=False):
    if steps is None or len(steps) == 0:
        return steps
    proof = Prover(
        axioms=all_axioms_to_prove,
        conditions=steps[0]["observation"]["ground_truth"], # 这个是steps[0]的ground_truth，也就是说，后面产生的新的ground_truth都没有被加入进来，只有make_up_conditions，我需要把一些一开始的condition给罗列进去
        objectives=steps[0]["observation"]["objectives"],
        prove_direction="backward"
    )

    if proof.is_proved():
        return None
    hypo_objective = proof.get_objectives()[0]
    translated_steps = list()
    iteration = 0
    while len(steps) > 0 and (not proof.is_proved()):
        iteration += 1
        if iteration >= 30:
            return None

        step = steps.pop()
        if step["lemma"].name == "EquivalenceSubstitution": # 这个好像是说，如果是EquivalenceSubstitution，那么就直接跳到下一步，也不是
            last_step = steps.pop()
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

        else:
            lemma = step["lemma"]
            operands = step["lemma"].prove_operands(hypo_objective)
            coding = step["original_coding"]
            transform_gt = step["transform_gt"]
            if transform_gt:
                transformed_side = step["transformed_side"]

        translated_steps.append(
            {
                "observation": proof.get_observation(),
                "lemma": lemma,
                "input_entities": operands
            }
        )
        proof.apply_theorem(theorem=lemma,
                            operands=operands, )
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
            hypo_objective = proof.get_objectives()[0]
        else:
            hypo_lhs = get_entity_from_ls_and_coding(hypo_objective, coding[0]) # 确实，需要coding的原因是，需要把这个entity从ls中取出来，不能是随意乱构造一个同名的entity，因为需要entity.root
            hypo_rhs = get_entity_from_ls_and_coding(hypo_objective, coding[1])

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
