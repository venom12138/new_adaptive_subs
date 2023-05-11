import random
from copy import deepcopy

from proof_system.logic_functions import necessary_logic_functions
from proof_system.meta_axiom import MetaAxiom, MetaOrderedAxiom
from proof_system.numerical_functions import necessary_numerical_functions
from proof_system.utils import is_structured, is_entity, is_ls_type, is_constant
from logic.logic import Entity

random.seed(0)

# 对于不等式，要么只有transform_gt，要么只有extend_core_gt
class IneqMoveTerm(MetaOrderedAxiom):
    def __init__(self):
        input_no = 2 # prove的时候有几个operands
        assumption_size, conclusion_size = 1, 1 # assumption有几条
        assumption_types = ["Equivalent"] # whether the assumptions are equalities or inequalities
        super(IneqMoveTerm, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,

                                            assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a + b >= c, then a >= c + (-b)
            :param operands: [a, b, c]
            :return: dict(Assumptions, Conclusions)
            """
            a, b, c, = operands
            a_copied1, a_copied2 = a, a
            b_copied1, b_copied2 = b, b
            c_copied1, c_copied2 = c, c
            a_and_b = necessary_numerical_functions["add"].execute_nf([a_copied1, b_copied1])
            assumption = necessary_logic_functions["BiggerOrEqual"].execute_lf([a_and_b, c_copied1])
            neg_b = necessary_numerical_functions["opp"].execute_nf([b_copied2])
            c_minus_b = necessary_numerical_functions["add"].execute_nf([c_copied2, neg_b])
            conclusion = necessary_logic_functions["BiggerOrEqual"].execute_lf([a_copied2, c_minus_b])
            assumptions = [assumption]
            conclusions = [conclusion]
        elif mode == "prove":
            """
            2 inputs [a, c + (-b)]
            a + b >= c => a >= c + (-b)
            """
            a, c_minus_b, = [deepcopy(op) for op in operands]
            if is_entity(a) and is_entity(c_minus_b) and is_structured(c_minus_b, "add") and \
                    is_structured(c_minus_b.operands[1], "opp"):
                c, minus_b, = c_minus_b.operands
                b, = minus_b.operands
                a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
                assumption = necessary_logic_functions["BiggerOrEqual"].execute_lf([a_and_b, c])
                assumptions = [assumption]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, c_minus_b])]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError

        return {"Assumptions": assumptions,
                "Conclusions": conclusions}

    @staticmethod
    def transform_gt(core_gt, entities):
        if is_ls_type(core_gt, "BiggerOrEqual") and is_structured(core_gt.operands[0], "add"):
            return {
                "action": True,
                "makeup": False,
                "operands": core_gt.operands[0].operands + [core_gt.operands[1]], # 对啊，没问题，这就是把这个core_gt的左边a+b和右边的c拿出来了
                "transformed_side": "custom",
                "custom_function": lambda x, y: x,
                "original_coding": None
            }
        else:
            return {
                "action": False
            }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        x + y >= b => x >= b + (-y)
        """
        return self.transform_gt(core_gt, entities)

    @staticmethod
    def original_coding():
        return

    @staticmethod
    def prove_operands(new_ls):
        lhs, rhs, = new_ls.operands
        return [lhs, rhs]


class SquareGEQZero(MetaOrderedAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 1, 1
        assumption_types = None
        super(SquareGEQZero, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,

                                            assumption_types=assumption_types)
        self.input_type = "equality" # "equality" or "inequality" or "mixed"
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a = b => a * b >= 0
            """
            zero = Entity("0", is_constant=True)
            a, b = operands
            a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b])
            assumptions = [necessary_logic_functions["Equivalent"].execute_lf([a, b])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_mul_b, zero])]
        elif mode == "prove":
            """
            1 input: [a * b]
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "mul"):
                a, b, = term.operands
                a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b])
                zero = Entity("0", is_constant=True)
                assumptions = [necessary_logic_functions["Equivalent"].execute_lf([a, b])]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_mul_b, zero])]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if core_gt.logic_function.name == "Equivalent":
            """
            a = b -> a * b >= 0
            """
            return {
                "action": True,
                "makeup": False,
                "operands": core_gt.operands,
            }
        else:
            return {
                "action": False,
            }

    @staticmethod
    def original_coding():
        lhs_coding = (0, 0)
        rhs_coding = (0, 1)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        a_mul_b, _, = new_ls.operands
        return [a_mul_b]


class FirstPrincipleOfInequality(MetaOrderedAxiom):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(FirstPrincipleOfInequality, self).__init__(input_no=input_no,
                                                        assumption_size=assumption_size,
                                                        conclusion_size=conclusion_size,
                                                        assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= b and c >= d, then a + c >= b + d
            :param operands: 4 operands [a, b, c, d]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a, b, c, d, = operands
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([c, d])]
            a_and_c = necessary_numerical_functions["add"].execute_nf([a, c])
            b_and_d = necessary_numerical_functions["add"].execute_nf([b, d])
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_and_c, b_and_d])]
        elif mode == "prove":
            """
            a >= b, c >= d => a + c >= b + d
            2 operands [a + c, b + d]
            """
            lhs, rhs = [deepcopy(op) for op in operands]
            if is_structured(lhs, "add") and is_structured(rhs, "add"):
                a, c, = lhs.operands
                b, d, = rhs.operands
                assump1 = necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])
                assump2 = necessary_logic_functions["BiggerOrEqual"].execute_lf([c, d])
                assumptions = [assump1, assump2]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {"Assumptions": assumptions, "Conclusions": conclusions}

    # 嗷 这个core_gt其实可以是bigger_or_equal，也可以是Equivalent
    def transform_gt(self, core_gt, entities):
        right_entities = [entity for entity in entities if entity.root.logic_function == "BiggerOrEqual" and
                            entity.parent_index == 0 and entity is entity.root.operands[0] and
                            entity is not core_gt.operands[0]]
        if len(right_entities) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        right_entity = random.choice(right_entities)
        return {
            "action": True,
            "makeup": False,
            "operands": core_gt.operands + right_entity.root.operands
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        a >= b (c + z >= d) => a + (c + z) >= b + d
        """
        return {
            "action": True,
            "makeup": True,
            "makeup_config": [{
                "requirement_type": "BiggerOrEqual",
                "a": random.choice(entities),
                "b": random.choice(entities)
            }],
            "operand_retrieval":
                lambda makeup_conclusions: core_gt.operands + makeup_conclusions[0].operands, # operand_retrieval是有makeup_config的时候的operands，起到同样的把operands取出来传给apply_th的作用
        }

    @staticmethod
    def original_coding():
        lhs_coding = (0, 0)
        rhs_coding = (1, 0)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        return new_ls.operands


class SecondPrincipleOfInequality(MetaOrderedAxiom):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = None
        super(SecondPrincipleOfInequality, self).__init__(input_no=input_no,
                                                        assumption_size=assumption_size,
                                                        conclusion_size=conclusion_size,
                                                        assumption_types=assumption_types)
        
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= b and c >= 0, then a * c >= b * c
            :param operands: 3 operands [a, b, c]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            zero_entity = Entity(name="0", is_constant=True)
            a, b, c, = operands
            a_times_c = necessary_numerical_functions["mul"].execute_nf([a, c])
            b_times_c = necessary_numerical_functions["mul"].execute_nf([b, c])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b]),
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([c, zero_entity])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_times_c, b_times_c])]
        elif mode == "prove":
            """
            2 inputs [a*c, b*c]
            a >= b, c >= 0 => a*c >= b*c
            """
            lhs, rhs, = [deepcopy(op) for op in operands]
            if is_entity(lhs) and is_entity(rhs) and is_structured(lhs, "mul") and is_structured(rhs, "mul") \
                    and lhs.operands[1].name == rhs.operands[1].name:
                a, c, = lhs.operands
                b, _, = rhs.operands
                zero_entity = Entity(name="0", is_constant=True)
                assump1 = necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])
                assump2 = necessary_logic_functions["BiggerOrEqual"].execute_lf([c, zero_entity])
                assumptions = [assump1, assump2]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([lhs, rhs])]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {"Assumptions": assumptions, "Conclusions": conclusions}

    def transform_gt(self, core_gt, entities):
        right_entities = [entity for entity in entities if entity.root.logic_function == "BiggerOrEqual" and
                        entity.parent_index == 0 and entity is entity.root.operands[0] and
                        entity is not core_gt.operands[0] and entity.root.operands[1].name == "0"]
        if len(right_entities) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        right_entity = random.choice(right_entities)
        return {
            "action": True,
            "makeup": False,
            "operands": core_gt.operands + [right_entity.root.operands[0]] # core_gt是个等式，也就是a，b; right_entity就是那个大于0的c
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        
        assert is_ls_type(core_gt, "BiggerOrEqual") or is_ls_type(core_gt, "Bigger")
        """
        a >= b (c + x >= 0) -> a * (c+x) >= b * (c+x)
        """
        zero = Entity("0", is_constant=True)
        return {
            "action": True,
            "makeup": True,
            "makeup_config": [{
                "requirement_type": "BiggerOrEqual",
                "a": random.choice(entities),
                "b": zero,
            }],
            "operand_retrieval":
                lambda makeup_conclusions: core_gt.operands + [makeup_conclusions[0].operands[0]],
        }

    @staticmethod
    def original_coding():
        lhs_coding = (0, 0)
        rhs_coding = (1, 0)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        return new_ls.operands


class EquivalenceImpliesDoubleInequality(MetaOrderedAxiom):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 1, 1
        assumption_types = None
        super(EquivalenceImpliesDoubleInequality, self).__init__(input_no=input_no,
                                                                assumption_size=assumption_size,
                                                                conclusion_size=conclusion_size,

                                                                assumption_types=assumption_types)
        self.input_type = "equality" # "equality" or "inequality" or "mixed"
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a = b, then a >= b
            :param operands: 2 operands [a, b]
            :return: dict(Assumptions, Conclusions and ExtraEntities)
            """
            a, b, = operands
            assumptions = [necessary_logic_functions["Equivalent"].execute_lf([a, b])]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])]
        elif mode == "prove":
            """
            a = b => a >= b
            2 operand: [a, b]
            """
            a, b, = [deepcopy(op) for op in operands]
            equation = necessary_logic_functions["Equivalent"].execute_lf([a, b])
            assumptions = [equation]
            conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])]
        else:
            raise NotImplementedError
        return {"Assumptions": assumptions, "Conclusions": conclusions}

    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        a = b => a >= b
        """
        return {
            "action": True,
            "makeup": False,
            "operands": core_gt.operands,
        }

    @staticmethod
    def original_coding():
        return (0,), (1,)

    @staticmethod
    def prove_operands(new_ls):
        return new_ls.operands

class SecondLawOfIneqMoveTerm(MetaOrderedAxiom):
    def __init__(self):
        input_no = 2 # prove的时候有几个operands
        assumption_size, conclusion_size = 1, 1 # assumption有几条
        assumption_types = ["Equivalent"] # whether the assumptions are equalities or inequalities
        super(SecondLawOfIneqMoveTerm, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a >= b, then a + (-b) >= 0
            :param operands: [a, b]
            :return: dict(Assumptions, Conclusions)
            """
            a, b,  = operands
            zero_entity = Entity('0', is_constant=True)
            assumption = necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])
            negative_b = necessary_numerical_functions["opp"].execute_nf([b])
            a_plus_negative_b = necessary_numerical_functions["add"].execute_nf([a, negative_b])
            conclusion = necessary_logic_functions["BiggerOrEqual"].execute_lf([a_plus_negative_b, zero_entity])
            assumptions = [assumption]
            conclusions = [conclusion]
        elif mode == "prove":
            """
            2 inputs [a + (-b), 0]
            a >= b => a + (-b) >= 0
            """
            a_minus_b, zero_entity, = [deepcopy(op) for op in operands]
            if is_entity(a_minus_b) and is_entity(zero_entity) and (zero_entity.is_constant) and (zero_entity.name == '0') \
                and is_structured(a_minus_b, "add") and is_structured(a_minus_b.operands[1], "opp"):
                a, minus_b, = a_minus_b.operands
                b, = minus_b.operands
                assumption = necessary_logic_functions["BiggerOrEqual"].execute_lf([a, b])
                assumptions = [assumption]
                conclusions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a_minus_b, zero_entity])]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError

        return {"Assumptions": assumptions,
                "Conclusions": conclusions}

    @staticmethod
    def transform_gt(core_gt, entities):
        if is_ls_type(core_gt, "BiggerOrEqual"):
            return {
                "action": True,
                "makeup": False,
                "operands": [core_gt.operands[0], core_gt.operands[1]], 
                "original_coding": None
            }
        else:
            return {
                "action": False
            }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        a >= b => a + (-b) >= 0
        """
        return self.transform_gt(core_gt, entities)

    @staticmethod
    def original_coding():
        return

    @staticmethod
    def prove_operands(new_ls):
        lhs, rhs, = new_ls.operands
        return [lhs, rhs]

ordered_field_additional_axioms = {
    "SquareGEQZero": SquareGEQZero(),
    "EquivalenceImpliesDoubleInequality": EquivalenceImpliesDoubleInequality(),
    "FirstPrincipleOfInequality": FirstPrincipleOfInequality(),
    "SecondPrincipleOfInequality": SecondPrincipleOfInequality(),
    "IneqMoveTerm": IneqMoveTerm(),
    "SecondLawOfIneqMoveTerm": SecondLawOfIneqMoveTerm()
    # new add
    # "InverseInequality": InverseInequality(),
}
