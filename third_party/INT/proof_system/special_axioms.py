import random
from copy import deepcopy

from logic.logic import Entity
from proof_system.logic_functions import necessary_logic_functions
from proof_system.meta_axiom import MetaAxiom
from proof_system.numerical_functions import necessary_numerical_functions
from proof_system.utils import side_of_an_entity, search_operator_operands_in_gt, is_entity, is_structured, substitution, \
    is_ls_type, is_constant, opposite_simplify

random.seed(0)


# This file contains Equivalence Substitution, a special axiom only used to assist generation and not used in proof
# This theorem is very special, in that it's actually a macro action
class EquivalenceSubstitution(MetaAxiom):
    def __init__(self):
        input_no = 2
        assumption_types = []
        super(EquivalenceSubstitution, self).__init__(input_no=input_no,
                                                      assumption_size=2,
                                                      conclusion_size=1,
                                                      assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        """
        If a = b, then
        f is the function a is in, g is the function b is in
        1. f(a) => f(b)
        2. g(a) => g(b)
        :param operands: 2 operands [a, b]
        :param mode: generate or prove
        :return: dict(Assumptions, Conclusions)
        """
        a, b, = operands # a是待替换的, b是替换的

        # First set of assumption-conclusion pair
        gt_a = a.root
        assumptions_1 = [gt_a, necessary_logic_functions["Equivalent"].execute_lf([a, b])]
        gt_a_equivalent = deepcopy(gt_a)
        gt_a_equivalent.indexing()
        a_parent_node = gt_a_equivalent.ent_dic[a.parent_index]
        for ind, operand in enumerate(a_parent_node.operands): # 但是这个仅仅只是替换了a的父节点下面的子节点,没有替换其他的欸
            if operand.index == a.index:
                replace_ind = ind
                a_parent_node.operands[replace_ind] = deepcopy(b)
            else:
                pass
        gt_a_equivalent.update_name()
        conclusions_1 = [gt_a_equivalent]

        return {
            "Assumptions": assumptions_1,
            "Conclusions": conclusions_1
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        return {
            "action": False
        }

    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "mul")
        suitable_operands = [(operands[0],) for operands in all_operands if
                            operands[1].name == "inv" + " ( " + operands[0].name + " )"]
        if len(suitable_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        operands = random.choice(suitable_operands)
        transformed_side = side_of_an_entity(operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[operands[0].parent_index], proof_conclusion.operands[1]],
            "transformed_side": transformed_side,
            "original_coding": None
        }

    @staticmethod
    def original_coding():
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        raise NotImplementedError


# 需要判断的只有两种情况，一种是两个operands都是constant，另一种是被opp包裹的constant
# 这个也应该作为一个special_axiom
class AdditionSplit(MetaAxiom):
    def __init__(self,):
        """
        x + y = (x+y)
        """
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = [] # TODO：这里暂时先不考虑
        super(AdditionSplit, self).__init__(input_no=input_no,
                                        assumption_size=assumption_size,
                                        conclusion_size=conclusion_size,
                                        assumption_types=assumption_types)
    
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
                x + y = (x+y)
                :param operands: 2 inputs [x, y]
                :param mode: generate
                :return: dict(Assumptions, Conclusions)
            """
            x, y = operands
            num_x, opp_x = opposite_simplify(x)
            num_y, opp_y = opposite_simplify(y)
            if num_x == None or num_y == None:
                assumptions = []
                conclusions = []
            else:
                assumptions = []
                lhs = necessary_numerical_functions["add"].execute_nf([x, y])
                rhs = Entity(str(int(x.name) + int(y.name)), is_constant=True)
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([lhs, rhs])]
        
        elif mode == "prove":
            raise NotImplementedError()
        
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    
    @staticmethod
    def original_coding():
        # Function h represented by coding
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        raise NotImplementedError