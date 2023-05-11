import random
from copy import deepcopy

from proof_system.logic_functions import necessary_logic_functions
from proof_system.meta_axiom import MetaAxiom, MetaTheorem
from proof_system.numerical_functions import necessary_numerical_functions
from proof_system.utils import is_structured, is_entity, is_ls_type, is_constant
from logic.logic import Entity

random.seed(0)

# a + b >= \sqrt{ab} + \sqrt{ab}
class AMGMInequality(MetaTheorem):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(AMGMInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= 0 and b >= 0, then a + b >= \root(ab) + \root(ab)
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            a, b = operands
            a_plus_b = necessary_numerical_functions["add"].execute_nf([a, b])
            a_times_b = necessary_numerical_functions["mul"].execute_nf([a, b])
            root_ab = necessary_numerical_functions["root"].execute_nf([a_times_b])
            two_root_ab = necessary_numerical_functions["add"].execute_nf([root_ab, root_ab])
            
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b, zero_entity])] # a>=0算core_gt, b>=0算assumption
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_plus_b, two_root_ab])]
        elif mode == "prove":
            """
            a >= 0, b >= 0 => a + b >= \root(ab) + \root(ab)
            2 operands [a + b, \root(a*b)+\root(a*b)]
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "add") and \
                is_structured(rhs, "add") and is_structured(rhs.operands[0], "root") and \
                is_structured(rhs.operands[1], "root") and (rhs.operands[0].name == rhs.operands[1].name) and \
                is_structured(rhs.operands[0].operands[0], "mul") and is_structured(rhs.operands[1].operands[0], "mul")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a = lhs.operands[0]
                lhs_b = lhs.operands[1]
                rhs_a = rhs.operands[0].operands[0].operands[0]
                rhs_b = rhs.operands[0].operands[0].operands[1]
                if lhs_a.name == rhs_a.name and lhs_b.name == rhs_b.name:
                    zero_entity = Entity(name="0", is_constant=True)
                    assumptions = [
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b, zero_entity]),
                    ]
                    conclusions = [
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])
                    ]

        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # core_gt是a >= 0
    # def extend_core_gt(self, core_gt, entities, transform_gt):
    #     assert is_ls_type(core_gt, "BiggerOrEqual")
    #     if core_gt.operands[1].name == "0":
    #         zero_entity = Entity(name="0", is_constant=True)
            
    #         return {
    #             "action": True,
    #             "makeup": True,
    #             "makeup_config": [{
    #                 "requirement_type": "BiggerOrEqual",
    #                 "a": random.choice(entities),
    #                 "b": zero_entity,
    #             }],
    #             "operand_retrieval":
    #                 lambda makeup_conclusions: [core_gt.operands[0]] + [makeup_conclusions[0].operands[0]],
    #         }
    #     else:
    #         return {
    #             "action":False
    #         }
            
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}}]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 2
        operands = []
        for ls in valid_ls:
            op = ls.operands[0]
            operands.append(op)
        return operands

# 只考虑positive的情形
class BernoulliInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(BernoulliInequality, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)
    
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= 0 and b >= 1, then \pow((1 + a), b) >= 1 + b*a
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            one_entity = Entity(name="1", is_constant=True)
            zero_entity = Entity(name="0", is_constant=True)
            a,b = operands
            one_plus_a = necessary_numerical_functions["add"].execute_nf([one_entity, a])
            pow_one_plus_a_b = necessary_numerical_functions["pow"].execute_nf([one_plus_a, b]) # (1 + a)^b
            b_mul_a = necessary_numerical_functions["mul"].execute_nf([b, a])
            one_pluc_b_mul_a = necessary_numerical_functions["add"].execute_nf([one_entity, b_mul_a])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b, one_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([pow_one_plus_a_b, one_pluc_b_mul_a])]
        
        elif mode == "prove":
            """
            a >= 0, b >= 1 => \pow((1 + a), b) >= 1 + b*a
            :param operands: 2 operands [\pow((1 + a), b), 1 + b*a]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "pow") and \
                    is_structured(rhs, "add") and is_structured(lhs.operands[0], "add") and \
                    lhs.operands[0].operands[0].name == "1" and rhs.operands[0].name == "1" and \
                    is_structured(rhs.operands[1], "mul")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a = lhs.operands[0].operands[1]
                lhs_b = lhs.operands[1]
                rhs_a = rhs.operands[1].operands[1]
                rhs_b = rhs.operands[1].operands[0]
                if lhs_a.name == rhs_a.name and lhs_b.name == rhs_b.name:
                    zero_entity = Entity(name="0", is_constant=True)
                    one_entity = Entity(name="1", is_constant=True)
                    assumptions = [
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b, one_entity]),
                    ]
                    conclusions = [
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])
                    ]
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'1':(1,)}}]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 2
        operands = []
        for ls in valid_ls:
            op = ls.operands[0]
            operands.append(op)
        return operands
    
class YoungInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2 # a^p * 1/p + b^q * 1/q, a * b
        assumption_size, conclusion_size = 5, 1
        assumption_types = None
        super(YoungInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= 0, b >= 0, p >= 0, q >= 0, and 1/p + 1/q = 1 then a^p * 1/p + b^q * 1/q >= a * b
            :param operands: 4 operands [a, b, p, q]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            one_entity = Entity(name="1", is_constant=True)
            a, b, p, q = operands
            pow_a_p = necessary_numerical_functions["pow"].execute_nf([a, p]) # a^p
            pow_b_q = necessary_numerical_functions["pow"].execute_nf([b, q]) # b^q
            inv_p = necessary_numerical_functions["inv"].execute_nf([p]) # 1/p
            inv_q = necessary_numerical_functions["inv"].execute_nf([q]) # 1/q
            a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b]) # a * b
            inv_p_add_inv_q = necessary_numerical_functions["add"].execute_nf([inv_p, inv_q]) # 1/p + 1/q
            pow_a_p_mul_inv_p = necessary_numerical_functions["mul"].execute_nf([pow_a_p, inv_p]) # a^p * 1/p
            pow_b_q_mul_inv_q = necessary_numerical_functions["mul"].execute_nf([pow_b_q, inv_q]) # b^q * 1/q
            lhs = necessary_numerical_functions["add"].execute_nf([pow_a_p_mul_inv_p, pow_b_q_mul_inv_q]) # a^p * 1/p + b^q * 1/q
            
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([p, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([q, zero_entity]),
                        necessary_logic_functions["Equivalent"].execute_lf([inv_p_add_inv_q, one_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, a_mul_b])]
        
        elif mode == "prove":
            """
            a >= 0, b >= 0, p >= 0, q >= 0, 1/p + 1/q = 1 => a^p * 1/p + b^q * 1/q >= a * b
            :param operands: 2 operands [a^p * 1/p + b^q * 1/q, a * b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "add") and is_structured(rhs, "mul") and \
                    is_structured(lhs.operands[0], "mul") and is_structured(lhs.operands[1], "mul") and \
                    is_structured(lhs.operands[0].operands[0], "pow") and is_structured(lhs.operands[0].operands[1], "inv") and \
                    is_structured(lhs.operands[1].operands[0], "pow") and is_structured(lhs.operands[1].operands[1], "inv")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a = lhs.operands[0].operands[0].operands[0]
                lhs_b = lhs.operands[1].operands[0].operands[0]
                lhs_p1 = lhs.operands[0].operands[0].operands[1]
                lhs_q1 = lhs.operands[1].operands[0].operands[1]
                lhs_p2 = lhs.operands[0].operands[1].operands[0]
                lhs_q2 = lhs.operands[1].operands[1].operands[0]
                rhs_a = rhs.operands[0]
                rhs_b = rhs.operands[1]
                if lhs_a.name == rhs_a.name and lhs_b.name == rhs_b.name and \
                    lhs_p1.name == lhs_p2.name and lhs_q1.name == lhs_q2.name:
                    zero_entity = Entity(name="0", is_constant=True)
                    one_entity = Entity(name="1", is_constant=True)
                    inv_p = necessary_numerical_functions["inv"].execute_nf([lhs_p1]) # 1/p
                    inv_q = necessary_numerical_functions["inv"].execute_nf([lhs_q1]) # 1/q
                    inv_p_add_inv_q = necessary_numerical_functions["add"].execute_nf([inv_p, inv_q]) # 1/p + 1/q
                    
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_p1, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_q1, zero_entity]),
                                necessary_logic_functions["Equivalent"].execute_lf([inv_p_add_inv_q, one_entity])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        return {"Assumptions": assumptions, "Conclusions": conclusions}

    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"Equivalent", 'structure_constraint':{(0,): 'add', (0,0): 'inv', (0,1): 'inv'}, 'operands_constraint':{'1':(1,)}}]
        operand_alignment = [{'ls_idx':[2, 4], 'operand_coding':[(0,), (0,0,0)]},
                            {'ls_idx':[3, 4], 'operand_coding':[(0,), (0,1,0)]}]
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 5
        operands = []
        for ls in valid_ls[:-1]:
            op = ls.operands[0]
            operands.append(op)
        return operands
    
class HolderInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2 # (a1^p + a2^p)^(1/p) * (b1^q + b2^q)^(1/q), a1 * b1 + a2 * b2
        assumption_size, conclusion_size = 7, 1
        assumption_types = None
        super(HolderInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)

    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            If a1>=0, a2>=0, b1>=0, b2>=0, p>=0, q>=0, 1/p + 1/q = 1, then (a1^p + a2^p)^(1/p) * (b1^q + b2^q)^(1/q) >= a1 * b1 + a2 * b2
            :param operands: 6 operands [a1, a2, b1, b2, p, q]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            one_entity = Entity(name="1", is_constant=True)
            a1, a2, b1, b2, p, q = operands
            pow_a1_p = necessary_numerical_functions["pow"].execute_nf([a1, p]) # a1^p
            pow_a2_p = necessary_numerical_functions["pow"].execute_nf([a2, p]) # a2^p
            pow_b1_q = necessary_numerical_functions["pow"].execute_nf([b1, q]) # b1^q
            pow_b2_q = necessary_numerical_functions["pow"].execute_nf([b2, q]) # b2^q
            inv_p = necessary_numerical_functions["inv"].execute_nf([p]) # 1/p
            inv_q = necessary_numerical_functions["inv"].execute_nf([q]) # 1/q
            inv_p_add_inv_q = necessary_numerical_functions["add"].execute_nf([inv_p, inv_q]) # 1/p + 1/q
            pow_a1_p_add_pow_a2_p = necessary_numerical_functions["add"].execute_nf([pow_a1_p, pow_a2_p]) # a1^p + a2^p
            pow_b1_q_add_pow_b2_q = necessary_numerical_functions["add"].execute_nf([pow_b1_q, pow_b2_q]) # b1^q + b2^q
            lhs_p = necessary_numerical_functions["pow"].execute_nf([pow_a1_p_add_pow_a2_p, inv_p]) # (a1^p + a2^p)^(1/p)
            lhs_q = necessary_numerical_functions["pow"].execute_nf([pow_b1_q_add_pow_b2_q, inv_q]) # (b1^q + b2^q)^(1/q)
            lhs = necessary_numerical_functions["mul"].execute_nf([lhs_p, lhs_q]) # (a1^p + a2^p)^(1/p) * (b1^q + b2^q)^(1/q)
            a1_mul_b1 = necessary_numerical_functions["mul"].execute_nf([a1, b1]) # a1 * b1
            a2_mul_b2 = necessary_numerical_functions["mul"].execute_nf([a2, b2]) # a2 * b2
            rhs = necessary_numerical_functions["add"].execute_nf([a1_mul_b1, a2_mul_b2]) # a1 * b1 + a2 * b2
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a1, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([a2, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b1, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b2, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([p, zero_entity]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([q, zero_entity]),
                        necessary_logic_functions["Equivalent"].execute_lf([inv_p_add_inv_q, one_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        elif mode == "prove":
            """
            a1>=0, a2>=0, b1>=0, b2>=0, p>=0, q>=0, 1/p + 1/q = 1 => (a1^p + a2^p)^(1/p) * (b1^q + b2^q)^(1/q) >= a1 * b1 + a2 * b2
            :param operands: 2 operands [(a1^p + a2^p)^(1/p) * (b1^q + b2^q)^(1/q), a1 * b1 + a2 * b2]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "mul") and is_structured(rhs, "add") and \
                    is_structured(lhs.operands[0], "pow") and is_structured(lhs.operands[1], "pow") and \
                    is_structured(lhs.operands[0].operands[0], "add") and is_structured(lhs.operands[1].operands[0], "add") and \
                    is_structured(lhs.operands[0].operands[1], "inv") and is_structured(lhs.operands[1].operands[1], "inv") and \
                    is_structured(lhs.operands[0].operands[0].operands[0], "pow") and is_structured(lhs.operands[0].operands[0].operands[1], "pow") and \
                    is_structured(lhs.operands[1].operands[0].operands[0], "pow") and is_structured(lhs.operands[1].operands[0].operands[1], "pow") and \
                    is_structured(rhs.operands[0], "mul") and is_structured(rhs.operands[1], "mul")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a1 = lhs.operands[0].operands[0].operands[0].operands[0] # a1
                lhs_a2 = lhs.operands[0].operands[0].operands[1].operands[0] # a2
                lhs_b1 = lhs.operands[1].operands[0].operands[0].operands[0] # b1
                lhs_b2 = lhs.operands[1].operands[0].operands[1].operands[0] # b2
                
                lhs_p1 = lhs.operands[0].operands[0].operands[0].operands[1] # p1
                lhs_p2 = lhs.operands[0].operands[0].operands[1].operands[1] # p2
                lhs_p3 = lhs.operands[0].operands[1].operands[0] # p3
                
                lhs_q1 = lhs.operands[1].operands[0].operands[0].operands[1] # q1
                lhs_q2 = lhs.operands[1].operands[0].operands[1].operands[1] # q2
                lhs_q3 = lhs.operands[1].operands[1].operands[0] # q3
                
                rhs_a1 = rhs.operands[0].operands[0] # a1
                rhs_b1 = rhs.operands[0].operands[1] # b1
                rhs_a2 = rhs.operands[1].operands[0] # a2
                rhs_b2 = rhs.operands[1].operands[1] # b2
                cond2 = (lhs_a1.name == rhs_a1.name) and (lhs_a2.name == rhs_a2.name) and \
                        (lhs_b1.name == rhs_b1.name) and (lhs_b2.name == rhs_b2.name) and \
                        (lhs_p1.name == lhs_p2.name) and (lhs_p1.name == lhs_p3.name) and \
                        (lhs_q1.name == lhs_q2.name) and (lhs_q1.name == lhs_q3.name)
                if cond2:
                    zero_entity = Entity(name="0", is_constant=True)
                    one_entity = Entity(name="1", is_constant=True)
                    inv_p = necessary_numerical_functions["inv"].execute_nf([lhs_p1]) # 1/p
                    inv_q = necessary_numerical_functions["inv"].execute_nf([lhs_q1]) # 1/q
                    inv_p_add_inv_q = necessary_numerical_functions["add"].execute_nf([inv_p, inv_q]) # 1/p + 1/q
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a1, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a2, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b1, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b2, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_p1, zero_entity]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_q1, zero_entity]),
                                necessary_logic_functions["Equivalent"].execute_lf([inv_p_add_inv_q, one_entity])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"Equivalent", 'structure_constraint':{(0,):'add', (0,0): 'inv', (0,1): 'inv'}, 'operands_constraint':{'1':(1,)}}]
        operand_alignment = [{'ls_idx':[4, 6], 'operand_coding':[(0,), (0,0,0)]},
                            {'ls_idx':[5, 6], 'operand_coding':[(0,), (0,1,0)]}]
        return constraints, operand_alignment

    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 7
        operands = []
        for ls in valid_ls[:-1]:
            op = ls.operands[0]
            operands.append(op)
        return operands

class ChebyshevSumInequality(MetaTheorem):
    def __init__(self):
        input_no = 2 # 2*(a1*b1 + a2*b2), (a1+a2) * (b1+b2)
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(ChebyshevSumInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            a1 >= a2, b1 >= b2 => 2*(a1*b1 + a2*b2) >= (a1+a2) * (b1+b2)
            :param operands: 2 operands [a1, a2, b1, b2]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a1, a2, b1, b2 = operands
            two_entity = Entity(name="2", is_constant=True)
            a1_mul_b1 = necessary_numerical_functions["mul"].execute_nf([a1, b1])
            a2_mul_b2 = necessary_numerical_functions["mul"].execute_nf([a2, b2])
            a1_mul_b1_add_a2_mul_b2 = necessary_numerical_functions["add"].execute_nf([a1_mul_b1, a2_mul_b2])
            lhs = necessary_numerical_functions["mul"].execute_nf([two_entity, a1_mul_b1_add_a2_mul_b2])
            a1_add_a2 = necessary_numerical_functions["add"].execute_nf([a1, a2])
            b1_add_b2 = necessary_numerical_functions["add"].execute_nf([b1, b2])
            rhs = necessary_numerical_functions["mul"].execute_nf([a1_add_a2, b1_add_b2])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a1, a2]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b1, b2])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        elif mode == "prove":
            """
            a1 >= a2, b1 >= b2 => 2*(a1*b1 + a2*b2) >= (a1+a2) * (b1+b2)
            :param operands: 2 operands [2*(a1*b1 + a2*b2), (a1+a2) * (b1+b2)]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "mul") and is_structured(rhs, "mul") and \
                    lhs.operands[0].name == "2" and is_structured(lhs.operands[1], "add") and \
                    is_structured(lhs.operands[1].operands[0], "mul") and is_structured(lhs.operands[1].operands[1], "mul") and \
                    is_structured(rhs.operands[0], "add") and is_structured(rhs.operands[1], "add")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a1 = lhs.operands[1].operands[0].operands[0] # a1
                lhs_b1 = lhs.operands[1].operands[0].operands[1] # b1
                lhs_a2 = lhs.operands[1].operands[1].operands[0] # a2
                lhs_b2 = lhs.operands[1].operands[1].operands[1] # b2
                
                rhs_a1 = rhs.operands[0].operands[0] # a1
                rhs_a2 = rhs.operands[0].operands[1] # a2
                rhs_b1 = rhs.operands[1].operands[0] # b1
                rhs_b2 = rhs.operands[1].operands[1] # b2
                
                if lhs_a1.name == rhs_a1.name and lhs_a2.name == rhs_a2.name and \
                    lhs_b1.name == rhs_b1.name and lhs_b2.name == rhs_b2.name:
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a1, lhs_a2]),
                                necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b1, lhs_b2])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        return {"Assumptions": assumptions, "Conclusions": conclusions}
        
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{}}]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 2
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
            operands.append(ls.operands[1])

        return operands
    
class ExponentialInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2
        assumption_size, conclusion_size = 1, 1
        assumption_types = None
        super(ExponentialInequality, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            c>=1 => x^c >= 1 + c * (x-1)
            :param operands: 2 operands [x, c]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            c, x = operands
            one_entity = Entity(name="1", is_constant=True)
            lhs = necessary_numerical_functions["pow"].execute_nf([x, c])
            opp_one = necessary_numerical_functions["opp"].execute_nf([one_entity])
            x_minus_one = necessary_numerical_functions["add"].execute_nf([x, opp_one])
            c_mul_x_minus_one = necessary_numerical_functions["mul"].execute_nf([c, x_minus_one])
            rhs = necessary_numerical_functions["add"].execute_nf([one_entity, c_mul_x_minus_one])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([c, one_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        elif mode == "prove":
            """
            c>=1 => x^c >= 1 + c * (x-1)
            :param operands: 2 operands [x^c, 1 + c * (x + (-1))]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "pow") and \
                    is_structured(rhs, "add") and is_structured(rhs.operands[1], "mul") and \
                    is_structured(rhs.operands[1].operands[1], "add") and \
                    is_structured(rhs.operands[1].operands[1].operands[1], "opp")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_x = lhs.operands[0]
                lhs_c = lhs.operands[1]
                rhs_one = rhs.operands[0]
                rhs_c = rhs.operands[1].operands[0]
                rhs_x = rhs.operands[1].operands[1].operands[0]
                rhs_one2 = rhs.operands[1].operands[1].operands[1].operands[0]
                if lhs_x.name == rhs_x.name and lhs_c.name == rhs_c.name and \
                    rhs_one.name == rhs_one2.name:
                    one_entity = Entity(name="1", is_constant=True)
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_c, one_entity])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]

        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'1':(1,)}},]
        operand_alignment = []
        return constraints, operand_alignment

    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 1
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
        operands.append(random.choice(entities))
        return operands
    
class MinkowskiInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2 # (a1^p + a2^p)^(1/p) + (b1^p + b2^p)^(1/p), ((a1+b1)^p + (a2+b2)^p)^(1/p)
        assumption_size, conclusion_size = 5, 1
        assumption_types = None
        super(MinkowskiInequality, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)
    
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            a1>=0, a2>=0, b1>=0, b2>=0, p>=1 => (a1^p + a2^p)^(1/p) + (b1^p + b2^p)^(1/p) >= ((a1+b1)^p + (a2+b2)^p)^(1/p)
            :param operands: 5 operands [a1, a2, b1, b2, p]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a1, a2, b1, b2, p = operands
            zero_entity = Entity(name="0", is_constant=True)
            one_entity = Entity(name="1", is_constant=True)
            pow_a1_p = necessary_numerical_functions["pow"].execute_nf([a1, p])
            pow_a2_p = necessary_numerical_functions["pow"].execute_nf([a2, p])
            pow_b1_p = necessary_numerical_functions["pow"].execute_nf([b1, p])
            pow_b2_p = necessary_numerical_functions["pow"].execute_nf([b2, p])
            pow_a1_p_add_pow_a2_p = necessary_numerical_functions["add"].execute_nf([pow_a1_p, pow_a2_p])
            pow_b1_p_add_pow_b2_p = necessary_numerical_functions["add"].execute_nf([pow_b1_p, pow_b2_p])
            inv_p = necessary_numerical_functions["inv"].execute_nf([p])
            lhs1 = necessary_numerical_functions["pow"].execute_nf([pow_a1_p_add_pow_a2_p, inv_p])
            lhs2 = necessary_numerical_functions["pow"].execute_nf([pow_b1_p_add_pow_b2_p, inv_p])
            lhs = necessary_numerical_functions["add"].execute_nf([lhs1, lhs2])
            a1_add_b1 = necessary_numerical_functions["add"].execute_nf([a1, b1])
            a2_add_b2 = necessary_numerical_functions["add"].execute_nf([a2, b2])
            pow_a1_add_b1_p = necessary_numerical_functions["pow"].execute_nf([a1_add_b1, p])
            pow_a2_add_b2_p = necessary_numerical_functions["pow"].execute_nf([a2_add_b2, p])
            rhs1 = necessary_numerical_functions["add"].execute_nf([pow_a1_add_b1_p, pow_a2_add_b2_p])
            rhs = necessary_numerical_functions["pow"].execute_nf([rhs1, inv_p])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a1, zero_entity]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([a2, zero_entity]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([b1, zero_entity]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([b2, zero_entity]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([p, one_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
            
        elif mode == "prove":
            """
            a1>=0, a2>=0, b1>=0, b2>=0, p>=1 => (a1^p + a2^p)^(1/p) + (b1^p + b2^p)^(1/p) >= ((a1+b1)^p + (a2+b2)^p)^(1/p)
            :param operands: 2 operands [(a1^p + a2^p)^(1/p) + (b1^p + b2^p)^(1/p), ((a1+b1)^p + (a2+b2)^p)^(1/p)]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "add") and \
                    is_structured(lhs.operands[0], "pow") and is_structured(lhs.operands[1], "pow") and \
                    is_structured(lhs.operands[0].operands[0], "add") and is_structured(lhs.operands[1].operands[0], "add") and \
                    is_structured(lhs.operands[0].operands[0].operands[0], "pow") and is_structured(lhs.operands[0].operands[0].operands[1], "pow") and \
                    is_structured(lhs.operands[1].operands[0].operands[0], "pow") and is_structured(lhs.operands[1].operands[0].operands[1], "pow") and \
                    is_structured(lhs.operands[0].operands[1], "inv") and is_structured(lhs.operands[1].operands[1], "inv") and \
                    is_structured(rhs, "pow") and is_structured(rhs.operands[0], "add") and \
                    is_structured(rhs.operands[1], "inv") and \
                    is_structured(rhs.operands[0].operands[0], "pow") and is_structured(rhs.operands[0].operands[1], "pow") and \
                    is_structured(rhs.operands[0].operands[0].operands[0], "add") and is_structured(rhs.operands[0].operands[1].operands[0], "add")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a1 = lhs.operands[0].operands[0].operands[0].operands[0]
                lhs_a2 = lhs.operands[0].operands[0].operands[1].operands[0]
                lhs_b1 = lhs.operands[1].operands[0].operands[0].operands[0]
                lhs_b2 = lhs.operands[1].operands[0].operands[1].operands[0]
                
                lhs_p1 = lhs.operands[0].operands[1].operands[0]
                lhs_p2 = lhs.operands[0].operands[0].operands[0].operands[1]
                lhs_p3 = lhs.operands[0].operands[0].operands[1].operands[1]
                lhs_p4 = lhs.operands[1].operands[1].operands[0]
                lhs_p5 = lhs.operands[1].operands[0].operands[0].operands[1]
                lhs_p6 = lhs.operands[1].operands[0].operands[1].operands[1]
                
                rhs_a1 = rhs.operands[0].operands[0].operands[0].operands[0]
                rhs_b1 = rhs.operands[0].operands[0].operands[0].operands[1]
                rhs_a2 = rhs.operands[0].operands[1].operands[0].operands[0]
                rhs_b2 = rhs.operands[0].operands[1].operands[0].operands[1]
                rhs_p1 = rhs.operands[1].operands[0]
                rhs_p2 = rhs.operands[0].operands[0].operands[1]
                rhs_p3 = rhs.operands[0].operands[1].operands[1]
                if lhs_a1.name == rhs_a1.name and lhs_a2.name == rhs_a2.name and lhs_b1.name == rhs_b1.name and lhs_b2.name == rhs_b2.name and \
                    lhs_p1.name == lhs_p2.name and lhs_p2.name == lhs_p3.name and lhs_p3.name == lhs_p4.name and lhs_p4.name == lhs_p5.name and \
                    lhs_p5.name == lhs_p6.name and lhs_p6.name == rhs_p1.name and rhs_p1.name == rhs_p2.name and rhs_p2.name == rhs_p3.name:
                    zero_entity = Entity(name="0", is_constant=True)
                    one_entity = Entity(name="1", is_constant=True)
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a1, zero_entity]),
                                    necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_a2, zero_entity]),
                                    necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b1, zero_entity]),
                                    necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_b2, zero_entity]),
                                    necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs_p1, one_entity])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                       {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                       {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                       {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                       {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'1':(1,)}},]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 5
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
        return operands

class JensenInequality(MetaTheorem):
    def __init__(self,):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(JensenInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            a > 0, b > 0 => root(1/2 * (a + b)) >= 1/2 * (root(a) + root(b))
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            two_entity = Entity(name="2", is_constant=True)
            a, b = operands
            a_add_b = necessary_numerical_functions["add"].execute_nf([a, b])
            inv_two = necessary_numerical_functions["inv"].execute_nf([two_entity])
            inv_two_a_add_b = necessary_numerical_functions["mul"].execute_nf([inv_two, a_add_b])
            log_inv_two_mul_a_add_b = necessary_numerical_functions["root"].execute_nf([inv_two_a_add_b])
            log_a = necessary_numerical_functions["root"].execute_nf([a])
            log_b = necessary_numerical_functions["root"].execute_nf([b])
            log_a_add_log_b = necessary_numerical_functions["add"].execute_nf([log_a, log_b])
            inv_two_mul_log_a_add_log_b = necessary_numerical_functions["mul"].execute_nf([inv_two, log_a_add_log_b])
            assumptions = [necessary_logic_functions["Bigger"].execute_lf([a, zero_entity]),
                        necessary_logic_functions["Bigger"].execute_lf([b, zero_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([log_inv_two_mul_a_add_b, inv_two_mul_log_a_add_log_b])]
        
        elif mode == "prove":
            """
            a > 0, b > 0 => root(1/2 * (a + b)) >= 1/2 * (root(a) + root(b))
            :param operands: 2 operands [root(1/2 * (a + b)), 1/2 * (root(a) + root(b))]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "root") and is_structured(rhs, "mul") and \
                    is_structured(lhs.operands[0], "mul") and is_structured(rhs.operands[0], "inv") and is_structured(rhs.operands[1], "add") and \
                    is_structured(lhs.operands[0].operands[0], "inv") and is_structured(lhs.operands[0].operands[1], "add") and \
                    is_structured(rhs.operands[1].operands[0], "root") and is_structured(rhs.operands[1].operands[1], "root")
            assumptions = []
            conclusions = []
            if cond1:
                lhs_a = lhs.operands[0].operands[1].operands[0] 
                lhs_b = lhs.operands[0].operands[1].operands[1]
                lhs_two = lhs.operands[0].operands[0].operands[0]
                rhs_a = rhs.operands[1].operands[0].operands[0]
                rhs_b = rhs.operands[1].operands[1].operands[0]
                rhs_two = rhs.operands[0].operands[0]
                if lhs_a.name == rhs_a.name and lhs_b.name == rhs_b.name and lhs_two.name == rhs_two.name:
                    zero_entity = Entity(name="0", is_constant=True)
                    assumptions = [necessary_logic_functions["Bigger"].execute_lf([lhs_a, zero_entity]),
                                necessary_logic_functions["Bigger"].execute_lf([lhs_b, zero_entity])]
                    conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
        return {"Assumptions": assumptions, "Conclusions": conclusions}
                
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"Bigger", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},
                        {'ls_type':"Bigger", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 2
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
        return operands

class InverseInequality(MetaTheorem):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 1, 1
        assumption_types = None
        super(InverseInequality, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)
    
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a > 0 , then 1/a > 0
            :param operands: 1 operands [a, ]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            a, = operands
            if a.name == "0":
                assumptions = []
                conclusions = []
            else:
                assumptions = [necessary_logic_functions["Bigger"].execute_lf([a, zero_entity])]
                inv_a = necessary_numerical_functions["inv"].execute_nf([a])
                conclusions = [necessary_logic_functions["Bigger"].execute_lf([inv_a, zero_entity])]
        
        elif mode == "prove":
            """
            2 inputs [1/a, b]
            a > 0 => 1/a > 0
            """
            inv_a, b = [deepcopy(op) for op in operands]
            
            if is_entity(b) and b.name == "0" and is_entity(inv_a) and is_structured(inv_a, "inv") and inv_a.operands[0].name != "0":
                a = inv_a.operands[0]
                assumptions = [necessary_logic_functions["Bigger"].execute_lf([a, b])]
                conclusions = [necessary_logic_functions["Bigger"].execute_lf([inv_a, b])]
            else:
                assumptions = []
                conclusions = []
        
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"Bigger", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},]
        operand_alignment = []
        return constraints, operand_alignment
    
    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 1
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
        return operands
    
    # def extend_core_gt(self, core_gt, entities, transform_gt):
    #     # a > 0 => 1/a > 0
    #     assert is_ls_type(core_gt, "Bigger")
    #     a, b, = core_gt.operands # b就是0
    #     if b.name != "0" or a.name == "0":
    #         return {
    #             "action": False
    #         }
        
    #     return {
    #         "action": True,
    #         "makeup": False,
    #         "operands": [core_gt.operands[0], core_gt.operands[1]],
    #         "operand_retrieval":
    #             lambda makeup_conclusion: [core_gt.operands[0]], # TODO: operand_retrieval还需要改
    #     }
        
    # @staticmethod
    # def original_coding():
    #     lhs_coding = (0, 0)
    #     rhs_coding = (1, )
    #     return lhs_coding, rhs_coding

    # @staticmethod
    # def prove_operands(new_ls):
    #     return [new_ls.operands[0]]


class SquareRootInequality(MetaTheorem):
    def __init__(self):
        input_no = 2 # root(a), root(b)
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(SquareRootInequality, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            a>=b, b>=0 => root(a) >= root(b)
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a, b = operands
            root_a = necessary_numerical_functions["root"].execute_nf([a])
            root_b = necessary_numerical_functions["root"].execute_nf([b])
            zero_entity = Entity(name="0", is_constant=True)
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
                        necessary_logic_functions["BiggerOrEqual"].execute_lf([b, zero_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([root_a, root_b])]
        
        elif mode == "prove":
            """
            a>=b, b>=0 => root(a) >= root(b)
            :param operands: 2 operands [root(a), root(b)]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "root") and \
                    is_structured(rhs, "root")
            assumptions = []
            conclusions = []
            if cond1:
                a = lhs.operands[0]
                b = rhs.operands[0]
                zero_entity = Entity(name="0", is_constant=True)
                assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([b, zero_entity])]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{}},
                        {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},]
        operand_alignment = [{'ls_idx':[0, 1], 'operand_coding':[(1,), (0,)]}]
        return constraints, operand_alignment

    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 2
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
        return operands
    
# class LogInequality(MetaTheorem):
#     def __init__(self):
#         input_no = 2 # log(a), log(b)
#         assumption_size, conclusion_size = 2, 1 # a>=b, b>0
#         assumption_types = None
#         super(LogInequality, self).__init__(input_no=input_no,
#                                         assumption_size=assumption_size,
#                                         conclusion_size=conclusion_size,
#                                         assumption_types=assumption_types)
#     def execute_th(self, operands, mode):
#         if mode == "generate":
#             """
#             a>=b, b>0 => log(a) >= log(b)
#             :param operands: 2 operands [a, b]
#             :return: dict(Assumptions, Conclusions and ExtraEntities)
#             """
#             a, b = operands
#             log_a = necessary_numerical_functions["log"].execute_nf([a])
#             log_b = necessary_numerical_functions["log"].execute_nf([b])
#             zero_entity = Entity(name="0", is_constant=True)
#             assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
#                             necessary_logic_functions["Bigger"].execute_lf([b, zero_entity])]
#             conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([log_a, log_b])]
        
#         elif mode == "prove":
#             """
#             a>=b, b>0 => log(a) >= log(b)
#             :param operands: 2 operands [log(a), log(b)]
#             :return: dict(Assumptions, Conclusions and ExtraEntities)
#             """
#             lhs, rhs = [deepcopy(op) for op in operands]
#             cond1 = is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "log") and is_structured(rhs, "log")
#             assumptions = []
#             conclusions = []
#             if cond1:
#                 a = lhs.operands[0]
#                 b = rhs.operands[0]
#                 zero_entity = Entity(name="0", is_constant=True)
#                 assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
#                             necessary_logic_functions["Bigger"].execute_lf([b, zero_entity])]
#                 conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        
#         return {"Assumptions": assumptions, "Conclusions": conclusions}
    
#     # generate的时候，condition要求的constraint需要满足如下条件
#     def input_constraints(self, ):
#         constraints = [{'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{}},
#                         {'ls_type':"BiggerOrEqual", 'structure_constraint':{}, 'operands_constraint':{'0':(1,)}},]
#         operand_alignment = [{'ls_idx':[0, 1], 'operand_coding':[(1,), (0,)]}]
#         return constraints, operand_alignment

#     def get_operands_from_valid_ls(self, valid_ls, entities):
#         assert len(valid_ls) == 2
#         operands = []
#         for ls in valid_ls:
#             operands.append(ls.operands[0])
#         return operands
    
class BigtoBiggerInequality(MetaTheorem):
    def __init__(self):
        input_no = 2 # a, b
        assumption_size, conclusion_size = 1, 1
        assumption_types = None
        super(BigtoBiggerInequality, self).__init__(input_no=input_no,
                                                    assumption_size=assumption_size,
                                                    conclusion_size=conclusion_size,
                                                    assumption_types=assumption_types)
        
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            If a > b, then a >= b
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a, b = operands
            assumptions = [necessary_logic_functions["Bigger"].execute_lf([a, b])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])]
        
        elif mode == "prove":
            """
            a > b => a >= b
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            lhs, rhs, = [deepcopy(op) for op in operands]
            assumptions = []
            conclusions = []
            if is_entity(lhs) and is_entity(rhs):
                assumptions = [necessary_logic_functions["Bigger"].execute_lf([lhs, rhs])]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
        return {"Assumptions": assumptions, "Conclusions": conclusions}
    
    # generate的时候，condition要求的constraint需要满足如下条件
    def input_constraints(self, ):
        constraints = [{'ls_type':"Bigger", 'structure_constraint':{}, 'operands_constraint':{}},]
        operand_alignment = []
        return constraints, operand_alignment

    def get_operands_from_valid_ls(self, valid_ls, entities):
        assert len(valid_ls) == 1
        operands = []
        for ls in valid_ls:
            operands.append(ls.operands[0])
            operands.append(ls.operands[1])
        return operands
    
theorems = {        
    "AMGMInequality": AMGMInequality(),
    "BernoulliInequality": BernoulliInequality(),
    "YoungInequality": YoungInequality(),
    "HolderInequality": HolderInequality(),
    "ChebyshevSumInequality": ChebyshevSumInequality(),
    "ExponentialInequality": ExponentialInequality(),
    "MinkowskiInequality": MinkowskiInequality(),
    "JensenInequality": JensenInequality(),
    "InverseInequality": InverseInequality(),
    "SquareRootInequality": SquareRootInequality(),
    # "LogInequality": LogInequality(),
    "BigtoBiggerInequality": BigtoBiggerInequality()
}