from abc import ABC, abstractmethod
import random
from proof_system.utils import get_entity_from_ls_and_coding, is_structured, is_entity, \
                            construct_ls_from_constraint, is_ls_type, is_side_operands_constant
from copy import deepcopy
# 根据论文，只有当transform_gt用不了的时候，才会用extend_core_gt
# transform_gt是直接不引入新的entity，core_gt中本来就能应用这个axiom
# extend_core_gt是引入新的entity，core_gt中本来不具备能应用这个axiom的结构
# 先通过transform_gt或者extend_core_gt得到operands，然后通过execute_th得到conclusion
class MetaAxiom(ABC):
    def __init__(self, input_no, assumption_size, conclusion_size, assumption_types):
        """
        The design principle of the axioms extending core ground truths:
        L = R => f_l(L, c) = f_r(L, c) => L' = f_l(R, c) = f_r(L, c) = R'
        Therefore we can always recover L from L' and recover R from R'
        The how to extend function should provide h so that h(L'=R') = [L, R]
        It should also provide g such that g(L'=R') = operands used in prove mode
        :param input_no: the number of arguments the axiom takes
        :param assumption_size: how many assumptions the axiom will produce
        :param conclusion_size: how many conclusions the axiom will produce
        :param assumption_types: whether the assumptions are equalities or inequalities
        """
        self.input_no = input_no
        self.assumption_size = assumption_size
        self.conclusion_size = conclusion_size
        self.assumption_types = assumption_types
        self.name = self.__class__.__name__
        self.lemma_type = "axiom"
        self.input_type = "equality" # "equality" or "inequality" or "mixed"

    @abstractmethod
    def execute_th(self, operands, mode):
        raise NotImplementedError

    @abstractmethod
    def extend_core_gt(self, core_gt, entities, transform_gt):
        """Extend the core ground truth with the current lemma"""
        raise NotImplementedError

    @staticmethod
    def original_coding():
        """Function h represented by coding"""
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        """Function g"""
        raise NotImplementedError

class MetaOrderedAxiom(ABC):
    def __init__(self, input_no, assumption_size, conclusion_size, assumption_types):
        """
        The design principle of the axioms extending core ground truths:
        L = R => f_l(L, c) = f_r(L, c) => L' = f_l(R, c) = f_r(L, c) = R'
        Therefore we can always recover L from L' and recover R from R'
        The how to extend function should provide h so that h(L'=R') = [L, R]
        It should also provide g such that g(L'=R') = operands used in prove mode
        :param input_no: the number of arguments the axiom takes
        :param assumption_size: how many assumptions the axiom will produce
        :param conclusion_size: how many conclusions the axiom will produce
        :param assumption_types: whether the assumptions are equalities or inequalities
        """
        self.input_no = input_no
        self.assumption_size = assumption_size
        self.conclusion_size = conclusion_size
        self.assumption_types = assumption_types
        self.name = self.__class__.__name__
        self.lemma_type = "ordered_axiom"
        self.input_type = "inequality" # "equality" or "inequality" or "mixed"

    @abstractmethod
    def execute_th(self, operands, mode):
        raise NotImplementedError

    @abstractmethod
    def extend_core_gt(self, core_gt, entities, transform_gt):
        """Extend the core ground truth with the current lemma"""
        raise NotImplementedError

    @staticmethod
    def original_coding():
        """Function h represented by coding"""
        raise NotImplementedError

    @staticmethod
    def prove_operands(new_ls):
        """Function g"""
        raise NotImplementedError

class MetaTheorem(ABC):
    def __init__(self, input_no, assumption_size, conclusion_size, assumption_types):
        """
        The design principle of the theorems extending ground truths:
        given assumptions: a1, a2,...; c1, c2 = f(a1, a2)
        Therefore we can always recover L from L' and recover R from R'
        The how to extend function should provide h so that h(L'=R') = [L, R]
        It should also provide g such that g(L'=R') = operands used in prove mode
        :param input_no: the number of arguments the axiom takes
        :param assumption_size: how many assumptions the axiom will produce
        :param conclusion_size: how many conclusions the axiom will produce
        :param assumption_types: whether the assumptions are equalities or inequalities
        """
        self.input_no = input_no
        self.assumption_size = assumption_size
        self.conclusion_size = conclusion_size
        self.assumption_types = assumption_types
        self.name = self.__class__.__name__
        self.lemma_type = "theorem"
        self.input_type = "theorem" # "equality" or "inequality" or "mixed" or "theorem"

    @abstractmethod
    def execute_th(self, operands, mode):
        raise NotImplementedError
        

    # for generating theorems
    # find the logic statements satisfying the input constraints
    @abstractmethod
    def input_constraints(self,):
        """Input constraints"""
        # [{'ls_type':'Equivalent', 'structure_constraint':{'inv':(0,), 'add':()}, 'operands_constraint':{'0':(0,1), '1':(1,)}},
        #   {...}]
        raise NotImplementedError
    
    @abstractmethod
    def get_operands_from_valid_ls(self, valid_ls, entities):
        raise NotImplementedError()
    
    def filter_logic_statements_with_input_constraints(self, logic_statements):
        """Check whether the input logic statements satisfy the input constraints"""
        filtered_ls = len(self.input_constraints()[0]) * [None]
        operand_alignment = self.input_constraints()[1]
        idx_interfered_by_operand_alignment = [idx for align_rule in operand_alignment for idx in align_rule['ls_idx']]
        idx_interfered_by_operand_alignment = set(idx_interfered_by_operand_alignment)
        for ls in logic_statements:
            if None not in filtered_ls:
                break
            for idx, constraint in enumerate(self.input_constraints()[0]):
                if not is_ls_type(ls, constraint['ls_type']):
                    continue
                # 涉及到operand_alignment的idx不能是constant
                if idx in idx_interfered_by_operand_alignment:
                    if is_side_operands_constant(ls, 0):
                        continue
                structure_flag = True
                for coding, key in constraint['structure_constraint'].items():
                    if not is_structured(get_entity_from_ls_and_coding(ls, coding), key):
                        structure_flag = False
                        break
                if not structure_flag:
                    continue
                
                operand_flag = True
                for name, coding in constraint['operands_constraint'].items():
                    operand = get_entity_from_ls_and_coding(ls, coding)
                    if operand.name != name:
                        operand_flag = False
                if not operand_flag:
                    continue
                filtered_ls[idx] = ls
                break
        for align_rule in operand_alignment:
            ls_idxes = align_rule['ls_idx']
            operand_coding = align_rule['operand_coding']
            if filtered_ls[ls_idxes[0]] != None and filtered_ls[ls_idxes[1]] != None:
                op0 = deepcopy(get_entity_from_ls_and_coding(filtered_ls[ls_idxes[0]], operand_coding[0]))
                op1 = deepcopy(get_entity_from_ls_and_coding(filtered_ls[ls_idxes[1]], operand_coding[1]))
                if op0.name != op1.name:
                    filtered_ls[ls_idxes[0]] = None
                    filtered_ls[ls_idxes[1]] = None
        return filtered_ls
    
    # construct the logic statements with the input constraints
    # input: all the logic statements
    # return: logic statements satisfying the input constraints and the ls's status which is True if the ls is newly constructed
    # True的是新建立的ls
    def construct_ls_with_input_constraints(self, logic_statements, entities, check_solver=None):
        """Construct logic statements with the input constraints"""
        filtered_ls = self.filter_logic_statements_with_input_constraints(logic_statements) # logic_statements shouldn't be conflict
        # print(f"ls before filtering:{filtered_ls}")
        constraints, operand_alignment = self.input_constraints()

        filtered_ls_status = [False if ls != None else True for ls in filtered_ls]
        if None not in filtered_ls:
            return filtered_ls, filtered_ls_status
        
        idx_interfered_by_operand_alignment = [idx for align_rule in operand_alignment for idx in align_rule['ls_idx']]
        idx_interfered_by_operand_alignment = set(idx_interfered_by_operand_alignment)
        cnt = 0
        # print(f"check_solver:{check_solver.smt_solver}")
        cnt_constraint = 0
        # print(f"new construct")
        while None in filtered_ls:
            cnt += 1
            if cnt > 30:
                assert cnt_constraint >= 0
                for i in range(cnt_constraint):
                    check_solver.pop()
                return None, None
            for idx, ls in enumerate(filtered_ls):
                if ls == None:
                    if idx in idx_interfered_by_operand_alignment:
                        entities_not_constant = [ent for ent in entities if not ent.is_constant]
                        filtered_ents = entities_not_constant
                    else:
                        filtered_ents = entities
                    constructed_ls = construct_ls_from_constraint(constraints[idx], filtered_ents)
                    for align_rule in operand_alignment:
                        ls_idxes = align_rule['ls_idx']
                        operand_coding = align_rule['operand_coding']
                        if idx in ls_idxes:
                            cur_ls_idx_in_align_rule = ls_idxes.index(idx) # idx在align_rule的第一个还是第二个
                            another_ls_idx = list(set(ls_idxes)-{idx})[0] # 另一个ls的idx是几
                            ano_ls_idx_in_align_rule = ls_idxes.index(another_ls_idx) # 另一个ls的idx是在align_rule的第一个还是第二个
                            if filtered_ls[another_ls_idx] != None:
                                align_ent = deepcopy(get_entity_from_ls_and_coding(filtered_ls[another_ls_idx], operand_coding[ano_ls_idx_in_align_rule]))
                                constructed_ls.indexing()
                                operand_order = 'constructed_ls.'
                                for code in operand_coding[cur_ls_idx_in_align_rule][:-1]:
                                    operand_order = operand_order + f"operands[{code}]."
                                operand_order = operand_order + f"operands[{operand_coding[cur_ls_idx_in_align_rule][-1]}]"
                                exec(f"{operand_order} = align_ent")
                                constructed_ls.indexing()
                    try:
                        constraint_status, constraint_bool = check_solver.add_constraint(constructed_ls)
                        if constraint_status:
                            cnt_constraint += 1
                        if constraint_bool == 'Unknown':
                            if check_solver.check() == 'unsat':
                                if constraint_status == True:
                                    check_solver.pop()
                                    cnt_constraint -= 1
                                # assert check_solver.check() != 'unsat' # 非常影响效率
                                continue
                        elif constraint_bool == 'False':
                            assert constraint_status == False
                            continue
                        elif constraint_bool == 'True':
                            assert constraint_status == False
                        else:
                            raise NotImplementedError
                            
                        filtered_ls[idx] = constructed_ls
                    except:
                        # assert check_solver.check() != 'unsat' # 非常影响效率
                        constraint_status = False
                        continue
                    
        return filtered_ls, filtered_ls_status
    
    # print(f"cur_ls_idx_in_align_rule:{cur_ls_idx_in_align_rule}")
    # print(f"operand_coding:{operand_coding}")
    # print(f"cur_ent:{cur_ent}")
    # print(f"constraints[idx]:{constraints[idx]}")
    # print(f"constructed_ls:{constructed_ls}")
    
    # print(f"ls_idxes:{ls_idxes}")
    # print(f"idx:{idx}")
    # print(f"cur_ls_idx_in_align_rule:{cur_ls_idx_in_align_rule}")
    # print(f"another_ls_idx:{another_ls_idx}")
    # print(f"ano_ls_idx_in_align_rule:{ano_ls_idx_in_align_rule}")
    # print(f"operand_coding[cur_ls_idx_in_align_rule][-1]:{operand_coding[cur_ls_idx_in_align_rule][-1]}")
    # print(f"align_ent:{align_ent}")
    # print(f"idx:{idx}")
    # print(f"filtered_ls[another_ls_idx]:{filtered_ls[another_ls_idx]}")
    # print(f"operand_coding[ano_ls_idx_in_align_rule]:{operand_coding[ano_ls_idx_in_align_rule]}")
    # print(f"another_ls_idx:{another_ls_idx}")
    # print(f"target_operand:{eval(operand_order)}")
    # operand_order = 'constructed_ls'
    # print(f"constructed_ls:{constructed_ls}")
    # for code in operand_coding[cur_ls_idx_in_align_rule][:-1]:
    #     operand_order = operand_order + f".operands[{code}]"
    #     print(f"{operand_order}:{eval(operand_order)}")
    # # print(f"")
    # # print(f"cur_ent.operands[operand_coding[cur_ls_idx_in_align_rule][-1]]:{cur_ent.operands[operand_coding[cur_ls_idx_in_align_rule][-1]]}")
    # print('\n')
    # print(f"constructed_ls:{constructed_ls}")