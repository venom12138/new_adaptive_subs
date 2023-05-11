import random
from copy import deepcopy

from logic.logic import Entity
from proof_system.logic_functions import necessary_logic_functions
from proof_system.meta_axiom import MetaAxiom
from proof_system.numerical_functions import necessary_numerical_functions
from proof_system.utils import is_entity, is_structured, substitution, search_operator_operands_in_gt, \
    side_of_an_entity, is_ls_type, is_constant, opposite_simplify

random.seed(0)

# 因为这个生成theorem的时候，把equi，transitive，inequal分开了，所以好像就不太需要判定core_gt是个什么熊玩意
class AdditionCommutativity(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = []
        super(AdditionCommutativity, self).__init__(input_no=input_no,
                                                    assumption_size=assumption_size,
                                                    conclusion_size=conclusion_size,
                                                    assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
                a + b = b + a
                :param operands: 2 inputs [a, b]
                :param mode: generate
                :return: dict(Assumptions, Conclusions)
            """
            a, b = operands
            # 这个其实是返回了一个entity, name是add (a, b)
            a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
            
            b_and_a = necessary_numerical_functions["add"].execute_nf([b, a])
            assumptions = list()
            # 完全懂了，这个就是axiom应用到操作数上面，返回一个assumptions和conclusions，
            # conclusions就是将theorem应用到操作数上形成的equvalent的Logic_Statement
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a_and_b, b_and_a])]
        elif mode == "prove":
            """
                ls(a+b) => ls(b+a)
                :param operands: 1 inputs b + a
                :param mode: prove
                :return: dict(Assumptions, Conclusions)
            """
            b_and_a, = [deepcopy(op) for op in operands]
            if is_entity(b_and_a) and is_structured(b_and_a, "add"):
                b, a, = b_and_a.operands
                a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
                a_and_b_ls = substitution(b_and_a, a_and_b)
                assumptions = [a_and_b_ls]
                conclusions = [b_and_a.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    @staticmethod
    def transform_circle_back_names(operands):
        a, b, = operands
        return [b.name, a.name]

    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "add") # 获取所有的由add操作符组成的操作数,是一个tuple
        if len(all_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)
        else:
            if core_gt.logic_function.name == "Equivalent":
                operands = random.choice(all_operands)
                transformed_side = side_of_an_entity(operands[0])
                return {
                    "action": True,
                    "makeup": False,
                    "operands": operands, # 是一个tuple
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [core_gt.ent_dic[operands[0].parent_index], proof_conclusion.operands[1]], # operands是a, b的情况下， 这个的返回值就是a+b, b+a, 这个要做的就是把a+b替换成b+a
                    "transformed_side": transformed_side,
                    "circle_back_names": self.transform_circle_back_names(operands),
                    "original_coding": None
                }
            else:
                raise NotImplementedError
    # 这个extend_core_gt就是，core_gt是一个等式，把lhs中的相应的操作数用这个等式替换掉
    # 对于这个来说相当于是core_gt是a=b, axiom是a + c = c + a,
    # 用c替换掉了a，得到 b + c = c + a
    # transform是不引入新的entity，extend_core_gt是引入新的entity
    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        # 由于core_gt是一个等式，因此就有了要求的a=b，然后再用AdditionCommutativity，然后再做substitution就行了
        if core_gt.logic_function.name == "Equivalent":
            # a = b -> b + c = c + a
            return {
                "action": True,
                "makeup": False,
                "operands": [core_gt.operands[0], random.choice(entities)],
                "substitution_retrieval":
                    lambda makeup_conclusion, proof_conclusion: # proof_conclusions的00就是他操作的operands[0] （似乎就是core_gt.operands[0]阿
                    [proof_conclusion.operands[0].operands[0], core_gt.operands[1]] # 在operands是a, b(b是random choice出来的)，core_gt是a=c的情况下，这个的返回值就是a, c，但是这个其实想表达的其实就是[core_gt.operands[0],core_gt.operands[1]]
            }
        else:
            raise NotImplementedError

    @staticmethod
    def original_coding(): # b + c = c + a
        lhs_coding = (1, 1) # 这个original_coding其实是针对于extend_core_gt的,
        rhs_coding = (0, 0) # 因为这个会有一步substitution，所以(0,0)变成了b,(1,1)变成了a
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        lhs, rhs = new_ls.operands # 在extend_core_gt中，是把core_gt的lhs which is a+b, 拿出来变成了a+b=b+a,
        return [rhs]               # 然后新的core_gt变成rhs = b+a， 所以在prove的时候，拿出来的是new_ls的rhs
        


class AdditionAssociativity(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(AdditionAssociativity, self).__init__(input_no=input_no,
                                                    assumption_size=assumption_size,
                                                    conclusion_size=conclusion_size,
                                                    assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
                a + ( b + c ) = ( a + b ) + c
                :param operands: 3 inputs [a, b, c]
                :return: dict(Assumptions, Conclusions)
            """
            a, b, c = operands
            b_and_c = necessary_numerical_functions["add"].execute_nf([b, c])
            lhs = necessary_numerical_functions["add"].execute_nf([a, b_and_c])
            a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
            rhs = necessary_numerical_functions["add"].execute_nf([a_and_b, c])
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([lhs, rhs])]
        elif mode == "prove":
            """
                ls(a + ( b + c )) => ls(( a + b ) + c), or ls(( a + b ) + c) => ls(a + ( b + c ))
                :param operands: 1 inputs ((a+b) + c)
                :return: dict(Assumptions, Conclusions)
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "add") and is_structured(term.operands[0], "add"):
                # could be the first option
                first_add_operand, second_add_operand = term.operands
                a, b, = first_add_operand.operands
                b_and_c = necessary_numerical_functions["add"].execute_nf([b, second_add_operand])
                lhs = necessary_numerical_functions["add"].execute_nf([a, b_and_c])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "add") and is_structured(term.operands[1], "add"):
                # could be the second option
                first_add_operand, second_add_operand = term.operands
                b, c, = second_add_operand.operands
                a_and_b = necessary_numerical_functions["add"].execute_nf([first_add_operand, b])
                lhs = necessary_numerical_functions["add"].execute_nf([a_and_b, c])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "add")
        if len(all_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)

        correct_form_operands = []
        operands_as_single_entities = []
        for entity_pair in all_operands:
            operands_as_single_entities.extend(entity_pair)
        parent_entities = []
        for entity_pair in all_operands:
            parent_entities.append(core_gt.ent_dic[entity_pair[0].parent_index])
        for parent_entity in parent_entities:
            if parent_entity in operands_as_single_entities and parent_entity.parent_index != 0 and \
                    core_gt.ent_dic[parent_entity.parent_index].operands[1] is parent_entity:
                correct_form_operands.append(
                    (core_gt.ent_dic[parent_entity.parent_index].operands[0],
                    parent_entity.operands[0], parent_entity.operands[1])
                )

        if len(correct_form_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)

        operands = random.choice(correct_form_operands)
        transformed_side = side_of_an_entity(operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[operands[0].parent_index], proof_conclusion.operands[1]], # 这个的返回值其实就是 a + ( b + c ), ( a + b ) + c
            "transformed_side": transformed_side,
            "original_coding": None
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        # a=b -> b + ( c + d ) = ( a + c ) + d
        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]] + random.choices(entities, k=2),
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0].operands[0], core_gt.operands[1]]
        }

    @staticmethod
    def original_coding(): # 对于b + ( c + d ) = ( a + c ) + d
        lhs_coding = (1, 0, 0) # (1, 0, 0) 是a
        rhs_coding = (0, 0) # (0, 0) 是b
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands # 这个理由也是同上条axiom
        return [rhs]


class AdditionZero(MetaAxiom):
    def __init__(self):
        """
        This executes on behalf of AdditionLeftZero and AdditionRightZero
        """
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(AdditionZero, self).__init__(input_no=input_no,
                                           assumption_size=assumption_size,
                                           conclusion_size=conclusion_size,
                                           assumption_types=assumption_types)

    def execute_th(self, operands, mode="prove"):
        if mode == "generate":
            """
            a = 0 + a, or a = a + 0
            """
            a, b = operands
            assumptions = list()
            a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
            if b.name == "0":
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a, a_and_b])]
            elif a.name == "0":
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([b, a_and_b])]
            else:
                raise NotImplementedError

        elif mode == "prove":
            term, = [deepcopy(op) for op in operands]
            """
            ls(a) => ls(0+a), or ls(a) => ls(a+0)
            """
            if is_entity(term) and is_structured(term, "add") and term.operands[0].name == "0":
                zero, a, = term.operands
                lhs_ls = substitution(term, a)
                lhs_ls.indexing()
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "add") and term.operands[1].name == "0":
                a, zero, = term.operands
                lhs_ls = substitution(term, a)
                lhs_ls.indexing()
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
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
        """
        b = 0 + a, or b = a + 0
        :param core_gt:
        :param entities:
        :param transform_gt:
        :return:
        """
        zero_position = random.choice(["left", "right"])
        a = core_gt.operands[0]
        zero = Entity("0", is_constant=True)
        if zero_position == "left":
            operands = [zero, a]
            coding = [(1, 1), (0,)]
        elif zero_position == "right":
            operands = [a, zero]
            coding = [(1, 0), (0,)]
        else:
            raise NotImplementedError
        return {
            "action": True,
            "makeup": False,
            "operands": operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0], core_gt.operands[1]],
            "original_coding": coding
        }

    @staticmethod
    def original_coding():
        # Function h represented by coding
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        _, sum_of_a_and_zero, = new_ls.operands # 同上条axiom
        return [sum_of_a_and_zero]


class AdditionSimplification(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(AdditionSimplification, self).__init__(input_no=input_no,
                                                     assumption_size=assumption_size,
                                                     conclusion_size=conclusion_size,
                                                     assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            0 = a + (-a)
            :param operands: 1 inputs [a, ]
            :return: dict(Assumptions, Conclusions)
            """
            a, = operands
            minus_a = necessary_numerical_functions["opp"].execute_nf([a])
            a_and_minus_a = necessary_numerical_functions["add"].execute_nf([a, minus_a])
            zero = Entity(name="0", is_constant=True)
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([zero, a_and_minus_a])]
        elif mode == "prove":
            """
            a = b, ls(0) => ls(a + (-b))
            :param operands: 1 inputs [a + (-b)]
            """
            a_minus_b, = [deepcopy(op) for op in operands]
            if is_entity(a_minus_b) and is_structured(a_minus_b, "add") and is_structured(a_minus_b.operands[1], "opp"):
                a, minus_b, = a_minus_b.operands
                b, = minus_b.operands
                assump1 = necessary_logic_functions["Equivalent"].execute_lf([a, b])
                zero = Entity(name="0", is_constant=True)
                assump2 = substitution(a_minus_b, zero)
                assumptions = [assump1, assump2]
                conclusions = [a_minus_b.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    # 怪不得，因为没有用到这个函数
    # 这个函数有点问题啊，因为他找的是符合a + (-a)的输入，apply之后，得到proof_conclusion是0 = a + (-a)
    # 但是substitution居然是把a+(-a)替换成a+(-a)
    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "add")
        suitable_operands = [(operands[0],) for operands in all_operands if
                            operands[1].name == "opp" + " ( " + operands[0].name + " )"]
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

    # 条件: a = b， 没有transform_gt 
    def extend_core_gt(self, core_gt, entities, transform_gt):
        # if transform_gt:
        #     return self.transform_gt(core_gt, entities)
        # a = b -> 0 = a + (-b)
        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]],
            "substitution_retrieval": # proof_conclusion是0 = a + (-a), 他的operands[1].operands[1].operands[0]是a, core_gt的operands[1]是b，替换后得到0 = a + (-b) 
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[1].operands[1].operands[0], core_gt.operands[1]] 
        }

    @staticmethod
    def original_coding():
        lhs_coding = (1, 0)
        rhs_coding = (1, 1, 0)
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands # 同上条axiom
        return [rhs]

    def transform_recover_first_name(self, substitution_operands):
        # first_op, second_op, = substitution_operands
        # a, _, = first_op.operands
        # return a.name
        raise NotImplementedError


class MultiplicationCommutativity(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(MultiplicationCommutativity, self).__init__(input_no=input_no,
                                                          assumption_size=assumption_size,
                                                          conclusion_size=conclusion_size,
                                                          assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a * b = b * a
            :param operands: 2 inputs [a, b]
            :return: dict(Assumptions, Conclusions)
            """
            a, b = operands
            a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b])
            b_mul_a = necessary_numerical_functions["mul"].execute_nf([b, a])
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a_mul_b, b_mul_a])]
        elif mode == "prove":
            """
            ls(a*b) => ls(b*a)
            :param operands: 1 input [b*a]
            """
            b_mul_a, = [deepcopy(op) for op in operands]
            if is_entity(b_mul_a) and is_structured(b_mul_a, "mul"):
                b, a, = b_mul_a.operands
                a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b])
                lhs_ls = substitution(b_mul_a, a_mul_b)
                assumptions = [lhs_ls]
                conclusions = [b_mul_a.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    @staticmethod
    def transform_circle_back_names(operands):
        a, b, = operands
        return [b.name, a.name]

    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "mul")
        if len(all_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)
        else:
            if core_gt.logic_function.name == "Equivalent":
                operands = random.choice(all_operands)
                transformed_side = side_of_an_entity(operands[0])
                return {
                    "action": True,
                    "makeup": False,
                    "operands": operands,
                    "substitution_retrieval": # core_gt中是a * b，proof_conclusion是a * b = b * a，
                        lambda makeup_conclusion, proof_conclusion:
                        [core_gt.ent_dic[operands[0].parent_index], proof_conclusion.operands[1]],
                    "transformed_side": transformed_side,
                    "circle_back_names": self.transform_circle_back_names(operands),
                    "original_coding": None
                }
            else:
                raise NotImplementedError

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        non_zero_entities = [ent for ent in entities if ent.name != "0"]
        if len(non_zero_entities) == 0:
            non_zero_entities = entities
        if core_gt.logic_function.name == "Equivalent":
            # a = b -> b * c = c * a
            return {
                "action": True,
                "makeup": False,
                "operands": [core_gt.operands[0], random.choice(non_zero_entities)],
                "substitution_retrieval":
                    lambda makeup_conclusion, proof_conclusion:
                    [proof_conclusion.operands[0].operands[0], core_gt.operands[1]]
            }
        else:
            raise NotImplementedError

    @staticmethod
    def original_coding():
        lhs_coding = (1, 1)
        rhs_coding = (0, 0)
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands # 同上条axiom
        return [rhs]


class MultiplicationAssociativity(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(MultiplicationAssociativity, self).__init__(input_no=input_no,
                                                          assumption_size=assumption_size,
                                                          conclusion_size=conclusion_size,
                                                          assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a * ( b * c ) = ( a * b ) * c
            :param operands: 3 inputs [a, b, c]
            :return: dict(Assumptions, Conclusions)
            """
            a, b, c = operands
            a_copied1, a_copied2 = a, a
            b_copied1, b_copied2 = b, b
            c_copied1, c_copied2 = c, c
            b_and_c = necessary_numerical_functions["mul"].execute_nf([b_copied1, c_copied1])
            lhs = necessary_numerical_functions["mul"].execute_nf([a_copied1, b_and_c])
            a_and_b = necessary_numerical_functions["mul"].execute_nf([a_copied2, b_copied2])
            rhs = necessary_numerical_functions["mul"].execute_nf([a_and_b, c_copied2])
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([lhs, rhs])]
        elif mode == "prove":
            """
            ls(a * ( b * c )) => ls(( a * b ) * c), or ls(( a * b ) * c) -> ls(a * ( b * c ))
            :param operands: 1 input [(a*b)*c]
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "mul") and is_structured(term.operands[0], "mul"):
                # Could be the first option
                first_mul_operand, second_mul_operand, = term.operands
                a, b, = first_mul_operand.operands
                b_mul_c = necessary_numerical_functions["mul"].execute_nf([b, second_mul_operand])
                lhs = necessary_numerical_functions["mul"].execute_nf([a, b_mul_c])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and is_structured(term.operands[1], "mul"):
                # Could be second option
                first_mul_operand, second_mul_operand, = term.operands
                b, c, = second_mul_operand.operands
                a_mul_b = necessary_numerical_functions["mul"].execute_nf([first_mul_operand, b])
                lhs = necessary_numerical_functions["mul"].execute_nf([a_mul_b, c])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def transform_gt(self, core_gt, entities):
        all_operands = search_operator_operands_in_gt(core_gt, "mul")
        if len(all_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)

        correct_form_operands = []
        operands_as_single_entities = []
        for entity_pair in all_operands:
            operands_as_single_entities.extend(entity_pair)
        parent_entities = []
        for entity_pair in all_operands:
            parent_entities.append(core_gt.ent_dic[entity_pair[0].parent_index])
        for parent_entity in parent_entities:
            if parent_entity in operands_as_single_entities and parent_entity.parent_index != 0 and \
                    core_gt.ent_dic[parent_entity.parent_index].operands[1] is parent_entity:
                correct_form_operands.append(
                    (core_gt.ent_dic[parent_entity.parent_index].operands[0],
                    parent_entity.operands[0], parent_entity.operands[1])
                )

        if len(correct_form_operands) == 0:
            return self.extend_core_gt(core_gt, entities, transform_gt=False)

        operands = random.choice(correct_form_operands)
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

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        non_zero_entities = [ent for ent in entities if ent.name != "0"]
        if len(non_zero_entities) == 0:
            non_zero_entities = entities
        # a = b ->  b * ( c * d ) = ( a * c ) * d
        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]] + random.choices(non_zero_entities, k=2),
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0].operands[0], core_gt.operands[1]]
        }

    @staticmethod
    def original_coding():
        lhs_coding = (1, 0, 0)
        rhs_coding = (0, 0)
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands # 同上条axiom
        return [rhs]


class MultiplicationOne(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(MultiplicationOne, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)

    def execute_th(self, operands, mode="prove"):
        if mode == "generate":
            """
            a = a * 1, or a = 1 * a
            :param operands: 2 inputs [a, 1] or [1, a]
            :return: dict(Assumptions, Conclusions)
            """
            a, b, = operands
            assumptions = list()
            if b.name == "1":
                a_times_b = necessary_numerical_functions["mul"].execute_nf([a, b])
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a, a_times_b])]
            elif a.name == "1":
                a_times_b = necessary_numerical_functions["mul"].execute_nf([a, b])
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([b, a_times_b])]
            else:
                raise NotImplementedError

        elif mode == "prove":
            term, = [deepcopy(op) for op in operands]
            # ls(a) -> ls(1 * a), or ls(a) -> ls(a * 1)
            if is_entity(term) and is_structured(term, "mul") and term.operands[0].name == "1":
                _, a, = term.operands
                lhs_ls = substitution(term, a)
                lhs_ls.indexing()
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and term.operands[1].name == "1":
                a, _, = term.operands
                lhs_ls = substitution(term, a)
                lhs_ls.indexing()
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    # 前提是a = b, 然后才有a=b*1,所以没有transform_gt
    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        a = b -> b = 1 * a or b = a * 1
        :param core_gt:
        :param entities:
        :param transform_gt:
        :return:
        """
        one = Entity(name="1", is_constant=True)
        trivial_gt = necessary_logic_functions["Equivalent"].execute_lf([one, one])
        one = trivial_gt.operands[0]
        a = core_gt.operands[0]
        position_of_one = random.choice(["left", "right"])
        if position_of_one == "left":
            operands = [one, a]
            coding = [(1, 1), (0,)]
        elif position_of_one == "right":
            operands = [a, one]
            coding = [(1, 0), (0,)]
        else:
            raise NotImplementedError
        return {
            "action": True,
            "makeup": False,
            "operands": operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0], core_gt.operands[1]],
            "original_coding": coding
        }

    @staticmethod
    def original_coding():
        # Function h represented by coding
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        _, product, = new_ls.operands # 同上条axiom
        return [product]


class MultiplicationSimplification(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 2, 1
        assumption_types = ["Equivalent"]
        super(MultiplicationSimplification, self).__init__(input_no=input_no,
                                                           assumption_size=assumption_size,
                                                           conclusion_size=conclusion_size,
                                                           assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            1 = a * 1/a
            :param operands: 1 inputs [a, ]
            :return: dict(Assumptions, Conclusions)
            """
            a, = operands
            inv_a = necessary_numerical_functions["inv"].execute_nf([a])
            a_times_inv_a = necessary_numerical_functions["mul"].execute_nf([a, inv_a])
            one = Entity(name="1", is_constant=True)
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([one, a_times_inv_a])]
            if a.name == "0":
                conclusions = []
        elif mode == "prove": # 这个prove的时候，没有判断a和b都不是0,这个恐怕是在extend_core_gt里面保证的
            """
            a = b, ls(1) => ls(a * 1/b)
            :param 1 inputs [a * 1/b]
            """
            a_mul_inv_b, = [deepcopy(op) for op in operands]
            if is_entity(a_mul_inv_b) and is_structured(a_mul_inv_b, "mul") and \
                    is_structured(a_mul_inv_b.operands[1], "inv"):
                a, inv_b, = a_mul_inv_b.operands
                b, = inv_b.operands
                assump1 = necessary_logic_functions["Equivalent"].execute_lf([a, b])
                one = Entity(name="1", is_constant=True)
                assump2 = substitution(a_mul_inv_b, one) # 这个是把a_mul_inv_b中的a*1/b替换成1之后的ls
                assumptions = [assump1, assump2] # 要证的东西就变成了这个assump，原本的input所在的logic_statement就变成了结论
                conclusions = [a_mul_inv_b.root] # 这个是不做替换,直接就是operands所在的ls拿出来了
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
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
    # 其实这个也是只有extend_core_gt，没有transform_gt，因为并不会调用transform_gt
    def extend_core_gt(self, core_gt, entities, transform_gt):
        # a = b -> 1 = a * 1/b
        a, b, = core_gt.operands
        if a.name == "0" or b.name == "0":
            return {
                "action": False
            }

        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]],
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[1].operands[1].operands[0], core_gt.operands[1]]
        }

    @staticmethod
    def original_coding():
        lhs_coding = (1, 0)
        rhs_coding = (1, 1, 0)
        return [lhs_coding, rhs_coding]

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands # 同上条axiom
        return [rhs]

    def transform_recover_first_name(self, substitution_operands):
        # first_op, second_op, = substitution_operands
        # a, _, = first_op.operands
        # return a.name
        raise NotImplementedError


class AdditionMultiplicationLeftDistribution(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(AdditionMultiplicationLeftDistribution, self).__init__(input_no=input_no,
                                                                     assumption_size=assumption_size,
                                                                     conclusion_size=conclusion_size,
                                                                     assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            (c + d) * a = c * a + d * a
            :param operands: [a, c, d]
            :return:
            """
            a, c, d = operands
            # Construct the first conclusion
            c_and_d = necessary_numerical_functions["add"].execute_nf([c, d])
            lhs = necessary_numerical_functions["mul"].execute_nf([c_and_d, a])
            c_times_a = necessary_numerical_functions["mul"].execute_nf([c, a])
            d_times_a = necessary_numerical_functions["mul"].execute_nf([d, a])
            rhs = necessary_numerical_functions["add"].execute_nf([c_times_a, d_times_a])
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([lhs, rhs])] # 已有的=变换后的
        elif mode == "prove":
            """
            ls((c + d) * a) => ls(c * a + d * a), or ls(c * a + d * a) => ls((c + d) * a)
            :param operands: [c * a + d * a]
            :return:
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "add") and is_structured(term.operands[0], "mul") \
                    and is_structured(term.operands[1], "mul") \
                    and term.operands[0].operands[1].name == term.operands[1].operands[1].name:
                # Could be the first option
                c_mul_a, d_mul_a = term.operands
                c, a1, = c_mul_a.operands
                d, a2, = d_mul_a.operands
                c_and_d = necessary_numerical_functions["add"].execute_nf([c, d])
                lhs = necessary_numerical_functions["mul"].execute_nf([c_and_d, a1])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and is_structured(term.operands[0], "add"):
                # Could be the second option
                c_and_d, a, = term.operands
                c, d, = c_and_d.operands
                c_mul_a = necessary_numerical_functions["mul"].execute_nf([c, a])
                d_mul_a = necessary_numerical_functions["mul"].execute_nf([d, a])
                lhs = necessary_numerical_functions["add"].execute_nf([c_mul_a, d_mul_a])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def transform_gt(self, core_gt, entities):
        adding_operands = search_operator_operands_in_gt(core_gt, "add")
        timing_operands = search_operator_operands_in_gt(core_gt, "mul")
        # 找到所有adding的爹
        # search_operator的返回值是一个tuple，tuple的内容是符合operator的entity的operands
        # 找到所有(a+b)*c形式的operands 
        adding_parents = [core_gt.ent_dic[operands[0].parent_index] for operands in adding_operands] 
        suitable_operands = list()
        for adding_parent in adding_parents:
            for timing_operand_pair in timing_operands:
                if adding_parent is timing_operand_pair[0]:
                    suitable_operands.append(
                        (timing_operand_pair[1], adding_parent.operands[0], adding_parent.operands[1])
                    )

        if len(suitable_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        chosen_operands = random.choice(suitable_operands)
        transformed_side = side_of_an_entity(chosen_operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": chosen_operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[chosen_operands[0].parent_index], proof_conclusion.operands[1]],
            "transformed_side": transformed_side,
            "original_coding": None
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        if core_gt.logic_function.name == "Equivalent":

            a_original = core_gt.operands[0]
            c_original, d_original = random.choices(entities, k=2)

            a_position = random.choice([0, 1, 2])
            if a_position == 0:
                # a = b -> (b + c) * d = a * d + c * d
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [c_original, a_original, d_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[0].operands[0], core_gt.operands[1]],
                    "original_coding": ((1, 0, 0), (0, 0, 0))
                }
            elif a_position == 1:
                # a = b -> (c + b) * d = c * d + a * d
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [c_original, d_original, a_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[0].operands[1], core_gt.operands[1]],
                    "original_coding": ((1, 1, 0), (0, 0, 1))
                }
            elif a_position == 2:
                # a = b -> (c + d) * b = c * a + d * a
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [a_original, c_original, d_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[1], core_gt.operands[1]],
                    "original_coding": ((1, 1, 1), (0, 1))
                }
            else:
                raise AssertionError
        else:
            raise NotImplementedError

    @staticmethod
    def original_coding():
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands
        return [rhs]


class AdditionMultiplicationRightDistribution(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(AdditionMultiplicationRightDistribution, self).__init__(input_no=input_no,
                                                                      assumption_size=assumption_size,
                                                                      conclusion_size=conclusion_size,
                                                                      assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a * (c + d) = a * c + a * d
            :param operands: [a, c, d]
            :return:
            """
            a, c, d = operands
            # Construct the first conclusion
            c_and_d = necessary_numerical_functions["add"].execute_nf([c, d])
            lhs = necessary_numerical_functions["mul"].execute_nf([a, c_and_d])
            a_times_c = necessary_numerical_functions["mul"].execute_nf([a, c])
            a_times_d = necessary_numerical_functions["mul"].execute_nf([a, d])
            rhs = necessary_numerical_functions["add"].execute_nf([a_times_c, a_times_d])
            assumptions = list()
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([lhs, rhs])]
        elif mode == "prove":
            """
            ls(a * (c + d)) => ls(a * c + a * d), or ls(a * c + a * d) => ls(a * (c + d))
            :param operands: [a*c + a*d]
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "add") and is_structured(term.operands[0], "mul") \
                    and is_structured(term.operands[1], "mul") \
                    and term.operands[0].operands[0].name == term.operands[1].operands[0].name:
                # Could be the first option
                a_mul_c, a_mul_d, = term.operands
                a1, c, = a_mul_c.operands
                a2, d, = a_mul_d.operands
                c_and_d = necessary_numerical_functions["add"].execute_nf([c, d])
                lhs = necessary_numerical_functions["mul"].execute_nf([a1, c_and_d])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and is_structured(term.operands[1], "add"):
                # Could be the second option
                a, c_and_d, = term.operands
                c, d, = c_and_d.operands
                a_mul_c = necessary_numerical_functions["mul"].execute_nf([a, c])
                a_mul_d = necessary_numerical_functions["mul"].execute_nf([a, d])
                lhs = necessary_numerical_functions["add"].execute_nf([a_mul_c, a_mul_d])
                lhs_ls = substitution(term, lhs)
                assumptions = [lhs_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def transform_gt(self, core_gt, entities):
        adding_operands = search_operator_operands_in_gt(core_gt, "add")
        timing_operands = search_operator_operands_in_gt(core_gt, "mul")
        adding_parents = [core_gt.ent_dic[operands[0].parent_index] for operands in adding_operands]
        suitable_operands = list()
        for adding_parent in adding_parents:
            for timing_operand_pair in timing_operands:
                if adding_parent is timing_operand_pair[1]:
                    suitable_operands.append(
                        (timing_operand_pair[0], adding_parent.operands[0], adding_parent.operands[1])
                    )
        if len(suitable_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        chosen_operands = random.choice(suitable_operands)
        transformed_side = side_of_an_entity(chosen_operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": chosen_operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[chosen_operands[0].parent_index], proof_conclusion.operands[1]],
            "transformed_side": transformed_side,
            "original_coding": None
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        if core_gt.logic_function.name == "Equivalent":
            a_original = core_gt.operands[0]
            c_original, d_original = random.choices(entities, k=2)

            a_position = random.choice([0, 1, 2])
            if a_position == 0:
                # b * (c + d) = a * c + a * d
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [a_original, c_original, d_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[0], core_gt.operands[1]],
                    "original_coding": ((1, 0, 0), (0, 0))
                }
            elif a_position == 1:
                # c * (b + d) = c * a + c * d
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [c_original, a_original, d_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[1].operands[0], core_gt.operands[1]],
                    "original_coding": ((1, 0, 1), (0, 1, 0))
                }
            elif a_position == 2:
                # c * (d + b) = c * d + c * a
                return {
                    "action": True,
                    "makeup": False,
                    "operands": [c_original, d_original, a_original],
                    "substitution_retrieval":
                        lambda makeup_conclusion, proof_conclusion:
                        [proof_conclusion.operands[0].operands[1].operands[1], core_gt.operands[1]],
                    "original_coding": ((1, 1, 1), (0, 1, 1))
                }
            else:
                raise AssertionError
        else:
            raise NotImplementedError

    @staticmethod
    def original_coding():
        # Function h represented by coding
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands
        return [rhs]


class SquareDefinition(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(SquareDefinition, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a * a = sqr(a) 
            :param operands: 1 input [a]
            :return: dict(Assumptions, Conclusions)
            """
            a, = operands
            assumptions = list()
            a_sqr = necessary_numerical_functions["sqr"].execute_nf([a])
            a_mul_a = necessary_numerical_functions["mul"].execute_nf([a, a])
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a_mul_a, a_sqr])]
        elif mode == "prove":
            """
            ls(a * a) => ls(sqr(a)), or ls(sqr(a)) => ls(a * a)
            :param operands: 1 input [a ^ 2]
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "sqr"):
                a, = term.operands
                a_mul_a = necessary_numerical_functions["mul"].execute_nf([a, a])
                # 这个就是把term所在的ls中，term的父节点的所有子节点的sqr_a替换为了a*a
                lhs_ls = substitution(term, a_mul_a) 
                assumptions = [lhs_ls]
                conclusions = [term.root] # 把新得到的ls返回作为conclusions
            elif is_entity(term) and is_structured(term, "mul") and term.operands[0].name == term.operands[1].name:
                a1, a2, = term.operands
                square_a = necessary_numerical_functions["sqr"].execute_nf([a1])
                square_a_ls = substitution(term, square_a)
                assumptions = [square_a_ls]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    def transform_gt(self, core_gt, entities):
        # 返回这个logic_statement中所有的符合operator_type的entity
        all_operands = search_operator_operands_in_gt(core_gt, "mul")
        valid_operands = [operands for operands in all_operands if operands[0].name == operands[1].name]
        if len(valid_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)

        operands = random.choice(valid_operands)
        transformed_side = side_of_an_entity(operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": [operands[0]],
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[operands[0].parent_index], proof_conclusion.operands[1]],
            "transformed_side": transformed_side,
            "original_coding": None
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        # a = b -> a * b = sqr(a)
        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]],
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0].operands[1], core_gt.operands[1]]
        }

    @staticmethod
    def original_coding():
        lhs_coding = (0, 0)
        rhs_coding = (0, 1)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        _, rhs, = new_ls.operands
        return [rhs]


class PrincipleOfEquality(MetaAxiom):
    def __init__(self):
        input_no = 3
        assumption_size, conclusion_size = 2, 1
        assumption_types = ["Equivalent"]
        super(PrincipleOfEquality, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a=b, c=d, then a + c = b + d
            :param operands: 4 inputs [a, b, c, d]
            :return: dict(Assumptions, Conclusions)
            """
            a, b, c, d = operands
            assumptions = [
                necessary_logic_functions["Equivalent"].execute_lf([a, b]),
                necessary_logic_functions["Equivalent"].execute_lf([c, d])
            ]
            a_and_c = necessary_numerical_functions["add"].execute_nf([a, c])
            b_and_d = necessary_numerical_functions["add"].execute_nf([b, d])
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a_and_c, b_and_d])]

        elif mode == "prove":
            """
            a=b, c=d，ls(a+c) => ls(b+d)
            :param operands: 3 inputs [a, c, b+d]
            :return: dict(Assumptions, Conclusions)
            """
            a, c, b_and_d = [deepcopy(op) for op in operands]
            if is_entity(a) and is_entity(c) and is_entity(b_and_d) and \
                    is_structured(b_and_d, "add"):
                b, d, = [deepcopy(op) for op in b_and_d.operands]
                a_and_c = necessary_numerical_functions["add"].execute_nf([a, c])
                first_con = necessary_logic_functions["Equivalent"].execute_lf([a, b])
                second_con = necessary_logic_functions["Equivalent"].execute_lf([c, d])
                third_con = substitution(b_and_d, a_and_c)
                assumptions = [first_con, second_con, third_con]
                conclusions = [b_and_d.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError

        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    # 这个是只能extend，没有办法transform_gt
    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        a = b (c=d) -> a + c = b + d
        """
        return {
            "action": True,
            "makeup": True,
            "makeup_config": [{
                "requirement_type": "Equivalent",
                "a": random.choice(entities),
                "b": random.choice(entities),
            }],
            "operand_retrieval":
                lambda makeup_conclusions: core_gt.operands + makeup_conclusions[0].operands
        }

    @staticmethod
    def original_coding():
        lhs_coding = (0, 0)
        rhs_coding = (1, 0)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        lhs, rhs, = new_ls.operands
        a, c, = lhs.operands
        return [a, c, rhs]


class EquMoveTerm(MetaAxiom):
    def __init__(self):
        input_no = 2
        assumption_size, conclusion_size = 2, 1
        assumption_types = ["Equivalent"]
        super(EquMoveTerm, self).__init__(input_no=input_no,
                                          assumption_size=assumption_size,
                                          conclusion_size=conclusion_size,
                                          assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            If a + b = c, then a = c + (-b)
            :param operands: [a, b, c]
            :return: dict(Assumptions, Conclusions)
            """
            a, b, c, = [deepcopy(op) for op in operands]
            a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
            assumption = necessary_logic_functions["Equivalent"].execute_lf([a_and_b, c])
            assumptions = [assumption]
            neg_b = necessary_numerical_functions["opp"].execute_nf([b])
            c_minus_b = necessary_numerical_functions["add"].execute_nf([c, neg_b])
            conclusion = necessary_logic_functions["Equivalent"].execute_lf([a, c_minus_b])
            conclusions = [conclusion]
        elif mode == "prove":
            """
            a + b = c, ls(a) => ls(c + (-b))
            2 inputs: [a, c + (-b)]
            """
            a, c_minus_b, = [deepcopy(op) for op in operands]
            if is_entity(a) and is_entity(c_minus_b) and is_structured(c_minus_b, "add") \
                    and is_structured(c_minus_b.operands[1], "opp"):
                c, minus_b, = c_minus_b.operands
                b, = minus_b.operands
                a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
                first_con = necessary_logic_functions["Equivalent"].execute_lf([a_and_b, c])
                second_con = substitution(c_minus_b, a)
                assumptions = [first_con, second_con]
                conclusions = [c_minus_b.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError

        return {"Assumptions": assumptions,
                "Conclusions": conclusions}

    @staticmethod
    def transform_gt(core_gt, entities):
        if is_ls_type(core_gt, "Equivalent") and is_structured(core_gt.operands[0], "add"):
            return {
                "action": True,
                "makeup": False,
                "operands": core_gt.operands[0].operands + [core_gt.operands[1]],
                "transformed_side": "custom",
                "custom_function": lambda x, y: x,
                "original_coding": None,
            }
        else:
            return {
                "action": False
            }
    # 所以说这条axiom只能对a+b=c这种形式进行推理，其他的就action为False了
    def extend_core_gt(self, core_gt, entities, transform_gt):
        """
        x + y = b -> x = b + (-y)
        """
        return self.transform_gt(core_gt, entities)

    @staticmethod
    def original_coding():
        return

    @staticmethod
    def prove_operands(new_ls):
        lhs, rhs, = new_ls.operands
        return [lhs, rhs]

    @staticmethod
    def transform_recover_first_name(substitution_operands):
        return substitution_operands[0].name

class RootDefinition(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 1, 1
        assumption_types = ["Equivalent"]
        super(RootDefinition, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a = root(a^2)
            :param operands: 1 input [a]
            :return: dict(Assumptions, Conclusions)
            
            """
            ope, = operands
            # a = root(a^2)
            zero_entity = Entity("0", is_constant=True)
            a_sqr = necessary_numerical_functions["sqr"].execute_nf([ope])
            root_a_sqr = necessary_numerical_functions["root"].execute_nf([a_sqr])
            assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([ope, zero_entity])]
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([ope, root_a_sqr])]
        elif mode == "prove":
            """
            ls(root(a^2)) => ls(a), or ls(a) => ls(root(a^2))
            :param operands: 1 input [a] or [root(a^2)]
            """
            term, = [deepcopy(op) for op in operands]
            zero_entity = Entity("0", is_constant=True)
            if is_entity(term) and is_structured(term, "root") and is_structured(term.operands[0], "sqr"):
                a_sqr, = term.operands
                a, = a_sqr.operands
                lhs_ls = substitution(term, a)
                assumptions = [lhs_ls, 
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity])]
                conclusions = [term.root]
            elif is_entity(term):
                a = term.operands
                a_sqr = necessary_numerical_functions["sqr"].execute_nf([a])
                root_a_sqr = necessary_numerical_functions["root"].execute_nf([a_sqr])
                root_a_ls = substitution(term, root_a_sqr)
                assumptions = [root_a_ls,
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity])]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }

    # def transform_gt(self, core_gt, entities):
    #     # 获取所有的满足大于等于0关系的entity，而且还不是core_gt的左操作数
    #     all_bigger_operands = [entity for entity in entities if entity.root.logic_function == "BiggerOrEqual" and 
    #                         entity.parent_index == 0 and entity is entity.root.operands[0] and 
    #                         entity is not core_gt.operands[0] and entity.root.operands[1].name == "0"]
    #     valid_operands = all_bigger_operands
    #     if len(valid_operands) == 0:
    #         return self.extend_core_gt(core_gt, entities, False)
    #         # zero = Entity("0", is_constant=True)
    #         # ope = random.choice(entities)
    #         # return {
    #         #     "action": True,
    #         #     "makeup": True,
    #         #     "makeup_config":[{
    #         #         "requirement_type": "BiggerOrEqual",
    #         #         "a": ope,
    #         #         "b": zero,
    #         #     }],
    #         #     # "operand_retrieval":
    #         #     #     lambda makeup_conclusions: makeup_conclusions[0].operands[0],
    #         #     "operands": [ope],
    #         #     "operand_retrieval":
    #         #         lambda makeup_conclusion:
    #         #         [makeup_conclusion[0].operands[0]],
    #         #     "substitution_retrieval":
    #         #         lambda makeup_conclusion, proof_conclusion:
    #         #         [core_gt.ent_dic[ope.index], proof_conclusion.operands[1]]
    #         # }
    #         # return self.extend_core_gt(core_gt, entities, False)
    #     operands = random.choice(valid_operands)
    #     transformed_side = side_of_an_entity(operands[0])
        
    #     return {
    #         "action": True,
    #         "makeup": False,
    #         "operands": [operands[0]],
    #         "substitution_retrieval": # TODO: 增加substitution_retrieval
    #             lambda makeup_conclusion, proof_conclusion:
    #             [core_gt.ent_dic[operands[0].index], proof_conclusion.operands[1]],
    #         "transformed_side": transformed_side,
    #         "original_coding": None
    #     }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        # if transform_gt:
        #     return self.transform_gt(core_gt, entities)
        zero = Entity("0", is_constant=True)
        ope = core_gt.operands[0]
        return {
            "action": True,
            "makeup": True,
            "makeup_config":[{
                "requirement_type": "BiggerOrEqual",
                "a": ope,
                "b": zero,
            }],
            "operand_retrieval":
                lambda makeup_conclusions: [makeup_conclusions[0].operands[0]],
            "operands": [ope],
            # "substitution_retrieval":
            #     lambda makeup_conclusion, proof_conclusion:
            #     [proof_conclusion.operands[0], core_gt.operands[1]] # a = root(a^2)变成b = root(a^2)
        }

    @staticmethod
    def original_coding():
        lhs_coding = (1, 0, 0)
        rhs_coding = (0, )
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        rhs = new_ls.operands[1]
        return [rhs]
        # raise NotImplementedError()

class RootSimplification(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(RootSimplification, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)

    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            root(a^2) = a
            :param operands: 1 input [root(a^2)]
            :return: dict(Assumptions, Conclusions)
            """
            ope, = operands
            if is_structured(ope, 'root'): # root(a^2) = a, 默认了root的表达式，不能再嵌套一层root
                if is_structured(ope.operands[0], 'sqr'):
                    zero_entity = Entity("0", is_constant=True)
                    a = ope.operands[0].operands[0]
                    assumptions = [necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity]),]
                    conclusions = [necessary_logic_functions["Equivalent"].execute_lf([ope, a])]
                else:
                    assumptions = []
                    conclusions = []
        elif mode == "prove":
            """
            ls(root(a^2)) => ls(a), or ls(a) => ls(root(a^2))
            :param operands: 1 input [a] or [root(a^2)]
            """
            term, = [deepcopy(op) for op in operands]
            zero_entity = Entity("0", is_constant=True)
            if is_entity(term) and is_structured(term, "root") and is_structured(term.operands[0], "sqr"):
                a_sqr, = term.operands
                a, = a_sqr.operands
                lhs_ls = substitution(term, a)
                assumptions = [lhs_ls, 
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity])]
                conclusions = [term.root]
            elif is_entity(term):
                a = term.operands
                a_sqr = necessary_numerical_functions["sqr"].execute_nf([a])
                root_a_sqr = necessary_numerical_functions["root"].execute_nf([a_sqr])
                root_a_ls = substitution(term, root_a_sqr)
                assumptions = [root_a_ls,
                            necessary_logic_functions["BiggerOrEqual"].execute_lf([a, zero_entity])]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
        
    def transform_gt(self, core_gt, entities):
        all_root_operands = search_operator_operands_in_gt(core_gt, "root")
        
        valid_root_operands = [root_ope for root_ope in all_root_operands if is_structured(root_ope.operands[0], "sqr")]
        valid_operands = valid_root_operands
        if len(valid_operands) == 0:
            return {
                "action": False,
                }
        operands = random.choice(valid_operands)
        transformed_side = side_of_an_entity(operands[0])
        
        return {
            "action": True,
            "makeup": False,
            "operands": [operands[0]],
            "substitution_retrieval": 
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[operands[0].index], proof_conclusion.operands[1]], # 将root(a^2)替换为a
            "transformed_side": transformed_side,
            "original_coding": None
        }

    def extend_core_gt(self, core_gt, entities, transform_gt):
        
        return self.transform_gt(core_gt, entities)

    @staticmethod
    def original_coding():
        return

    @staticmethod
    def prove_operands(new_ls):
        rhs = new_ls.operands[1]
        return rhs
        # raise NotImplementedError()


class NegativeDefinition(MetaAxiom):
    def __init__(self,):
        """
        -a = -1 * a
        """
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(NegativeDefinition, self).__init__(input_no=input_no,
                                                assumption_size=assumption_size,
                                                conclusion_size=conclusion_size,
                                                assumption_types=assumption_types)
    
    def execute_th(self, operands, mode):
        if mode == "generate":
            """
            -a = -1 * a
            :param operands: a
            :return: dict(Assumptions, Conclusions)
            """
            a, = operands
            assumptions = []
            neg_a = necessary_numerical_functions["opp"].execute_nf([a])
            one = Entity("1", is_constant=True)
            neg_one = necessary_numerical_functions["opp"].execute_nf([one])
            neg_one_mul_a = necessary_numerical_functions["mul"].execute_nf([neg_one, a])
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([neg_a, neg_one_mul_a])]

        elif mode == "prove":
            term, = [deepcopy(op) for op in operands]
            """
            ls(-a) => ls(-1 * a) or ls(-1 * a) => ls(-a)
            """
            if is_entity(term) and is_structured(term,"opp"): # term: -a
                one = Entity("1", is_constant=True)
                neg_one = necessary_numerical_functions["opp"].execute_nf([one])
                a = term.operands[0]
                neg_one_mul_a = necessary_numerical_functions["mul"].execute_nf([neg_one, a])
                lhs_ls = substitution(term, neg_one_mul_a) 
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and is_structured(term.operands[0], "opp") and \
                term.operands[0].operands[0].name == "1": # term: -1 * a
                a = term.operands[1]
                neg_a = necessary_numerical_functions["opp"].execute_nf([a])
                lhs_ls = substitution(term, neg_a)
                assumptions = [lhs_ls]
                conclusions = [term.root]
        else:
            raise NotImplementedError
        
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    
    def transform_gt(self, core_gt, entities):
        opp_operands = search_operator_operands_in_gt(core_gt, "opp")
        if len(opp_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)
        chosen_operands = random.choice(opp_operands) # opp_operands的形式是tuple(a)
        transformed_side = side_of_an_entity(chosen_operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": [chosen_operands[0]],
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[chosen_operands[0].parent_index], proof_conclusion.operands[1]], # 将-a替换为-1*a
            "transformed_side": transformed_side,
            "original_coding": None
        }
    # 直接就拿lhs的operands[0]
    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        # 仿写的SquareDefinition
        return {
            "action": True,
            "makeup": False,
            "operands": [core_gt.operands[0]],
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [proof_conclusion.operands[0].operands[0], core_gt.operands[1]], # 将-a = -1 * a替换为-b = -1 * a
        }
        
    @staticmethod
    def original_coding():
        lhs_coding = (1, 1)
        rhs_coding = (0, 0)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        rhs = new_ls.operands[1]
        return rhs
    
class NegativeSimplification(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 1, 1 # 这个assumption_size似乎是在说prove的时候会产生多少条assumptions
        assumption_types = ["Equivalent"] # TODO：这个不好说是不是Equivalent
        super(NegativeSimplification, self).__init__(input_no=input_no,
                                                    assumption_size=assumption_size,
                                                    conclusion_size=conclusion_size,
                                                    assumption_types=assumption_types)
    def execute_th(self, operands, mode="generate"):
        if mode == "generate":
            """
            a = --a
            :param operands: 1 inputs [a, ]
            :return: dict(Assumptions, Conclusions)
            """
            a, = operands
            opp_a = necessary_numerical_functions["opp"].execute_nf([a])
            opp_opp_a = necessary_numerical_functions["opp"].execute_nf([opp_a])
            assumptions = []
            conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a, opp_opp_a])]
        
        elif mode == "prove":
            """
            ls(--a) => ls(a) or ls(a) => ls(--a)
            """
            term, = [deepcopy(op) for op in operands]
            if is_entity(term) and is_structured(term, "opp") and \
                is_structured(term.operands[0], "opp"):
                assump = substitution(term, term.operands[0].operands[0])
                assumptions = [assump]
                conclusions = [term.root]
            elif is_entity(term):
                opp_term = necessary_numerical_functions["opp"].execute_nf([term])
                opp_opp_term = necessary_numerical_functions["opp"].execute_nf([opp_term])
                assump = substitution(term, opp_opp_term)
                assumptions = [assump]
                conclusions = [term.root]
            else:
                assumptions = []
                conclusions = []
        
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    
    # 找到任何一个entity都可以，因为generate是a = --a
    def transform_gt(self, core_gt, entities):
        chosen_operands = [random.choice(entities)]
        transformed_side = side_of_an_entity(chosen_operands[0])
        
        return {
            "action": True,
            "makeup": False,
            "operands": chosen_operands,
            "substitution_retrieval":
                lambda makeup_conclusion, proof_conclusion:
                [core_gt.ent_dic[chosen_operands[0].index], proof_conclusion.operands[1]],
            "transformed_side": transformed_side,
            "original_coding": None
        }
    
    def extend_core_gt(self, core_gt, entities, transform_gt):
        if transform_gt:
            return self.transform_gt(core_gt, entities)
        # a = b => b = --a
        if core_gt.logic_function.name == "Equivalent":
            return {
                "action": True,
                "makeup": False,
                "operands": [core_gt.operands[0]],
                "substitution_retrieval":
                    lambda makeup_conclusion, proof_conclusion:
                    [proof_conclusion.operands[0], core_gt.operands[1]] # 把a = --a，替换为b = --a
            }
        else:
            raise NotImplementedError
    
    @staticmethod
    def original_coding():
        lhs_coding = (1, 0, 0)
        rhs_coding = (0, )
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        rhs = new_ls.operands[1]
        return rhs


field_axioms = {
    "AdditionCommutativity": AdditionCommutativity(),
    "AdditionAssociativity": AdditionAssociativity(),
    "AdditionZero": AdditionZero(),
    "AdditionSimplification": AdditionSimplification(),
    "MultiplicationCommutativity": MultiplicationCommutativity(),
    "MultiplicationAssociativity": MultiplicationAssociativity(),
    "MultiplicationOne": MultiplicationOne(),
    "MultiplicationSimplification": MultiplicationSimplification(),
    "AdditionMultiplicationLeftDistribution": AdditionMultiplicationLeftDistribution(),
    "AdditionMultiplicationRightDistribution": AdditionMultiplicationRightDistribution(),
    "SquareDefinition": SquareDefinition(),
    "PrincipleOfEquality": PrincipleOfEquality(),
    "EquMoveTerm": EquMoveTerm(),
    # new add
    # "RootDefinition": RootDefinition(),
    # "RootSimplification": RootSimplification(),
    # "NegativeDefinition": NegativeDefinition(),
    # "NegativeSimplification": NegativeSimplification(),
}
# "MultiplicationZero": MultiplicationZero()

# 弃用
"""
class MultiplicationZero(MetaAxiom):
    def __init__(self):
        input_no = 1
        assumption_size, conclusion_size = 0, 1
        assumption_types = ["Equivalent"]
        super(MultiplicationZero, self).__init__(input_no=input_no,
                                            assumption_size=assumption_size,
                                            conclusion_size=conclusion_size,
                                            assumption_types=assumption_types)
    # 仿写的AdditionZero
    def execute_th(self, operands, mode):
        if mode == "generate":
            
            # 0 = a * 0, or 0 = 0 * a
            
            a, b = operands
            assumptions = []
            a_mul_b = necessary_numerical_functions["mul"].execute_nf([a, b])
            if b.name == "0":
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([b, a_mul_b])]
            elif a.name == "0":
                conclusions = [necessary_logic_functions["Equivalent"].execute_lf([a, a_mul_b])]
            else:
                raise NotImplementedError
        
        elif mode == "prove":
            term, = [deepcopy(op) for op in operands]
            
            # ls(0*a) => ls(0), or ls(a*0) => ls(0)
            
            if is_entity(term) and is_structured(term, "mul") and term.operands[0].name == "0":
                zero, a, = term.operands
                lhs_ls = substitution(term, zero)
                lhs_ls.indexing() # 有点多余
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
            elif is_entity(term) and is_structured(term, "mul") and term.operands[1].name == "0":
                a, zero, term.operands
                lhs_ls = substitution(term, zero)
                lhs_ls.indexing() # 有点多余
                lhs_ls.update_name()
                assumptions = [lhs_ls]
                conclusions = [term.root]
            
            else:
                assumptions = []
                conclusions = []
        else:
            raise NotImplementedError()
        return {
            "Assumptions": assumptions,
            "Conclusions": conclusions
        }
    
    # 找到所有0*a或者a*0的表达式
    # 暂时弃用这个函数
    def transform_gt(self, core_gt, entities):
        mul_operands = search_operator_operands_in_gt(core_gt, "mul")
        suitable_operands = [ope for ope in mul_operands if ope[0].name == "0" or ope[1].name == "0"]
        if len(suitable_operands) == 0:
            return self.extend_core_gt(core_gt, entities, False)
        
        operands = random.choice(suitable_operands)
        if operands[0].name == "0":
            transformed_side = side_of_an_entity(operands[1])
        else: 
            transformed_side = side_of_an_entity(operands[0])
        return {
            "action": True,
            "makeup": False,
            "operands": [operands[0], operands[1]],
            "substitution_retrieval":
                [NotImplementedError], # TODO：substitution还需要改
            "transformed_side": transformed_side,
            "original_coding": None
        }
    # 仅对于其中一项是0启用
    def extend_core_gt(self, core_gt, entities, transform_gt):
        
        # 0 = 0 * a, or 0 = a * 0
        # :param core_gt:
        # :param entities:
        # :param transform_gt:
        # :return:
        
        # if transform_gt:
        #     return self.transform_gt(core_gt, entities)
        
        zero_entity = Entity(name="0", is_constant=True)
        a = core_gt.operands[0]
        zero_position = random.choice(["left", "right"])
        if zero_position == "left":
            operands = [zero_entity, a]
            coding = [(1, 1), (0,)] # TODO 这里的coding还需要改
        elif zero_position == "right":
            operands = [a, zero_entity]
            coding = [(1, 0), (0,)]
        else:
            raise NotImplementedError
        
        return {
            "action": True,
            "makeup": False,
            "operands": operands,
            # "substitution_retrieval":
            #     lambda makeup_conclusion, proof_conclusion:
            #     [proof_conclusion.operands[0], proof_conclusion.operands[0]], # 无需替换
            "original_coding": coding
        }
        
    @staticmethod
    def original_coding():
        #TODO：这是我瞎编的
        lhs_coding = (0, 0)
        rhs_coding = (0, 1)
        return lhs_coding, rhs_coding

    @staticmethod
    def prove_operands(new_ls):
        raise NotImplementedError()
"""