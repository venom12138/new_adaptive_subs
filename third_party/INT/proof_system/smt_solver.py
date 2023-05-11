from pysmt.shortcuts import Symbol
from pysmt.shortcuts import Solver
from pysmt.typing import INT, REAL
import re
from visualization.latex_parse import extract_two_operands
from visualization.seq_parse import rm_function_and_brackets, entity_name_to_seq_string
from logic.logic import Entity, LogicStatement
from proof_system.logic_functions import necessary_logic_functions
from proof_system.numerical_functions import necessary_numerical_functions
from copy import deepcopy
import time

class smt_solver:
    def __init__(self,):
        self.smt_name2var = {}
        self.smt_assumptions = []
        self.smt_solver = Solver()
        self.total_time = 0
        
    def add_individual_entity(self, entity):
        if entity.name not in self.smt_name2var.keys() and not entity.is_constant:
            self.smt_name2var[entity.name] = Symbol(entity.name, REAL)
    
    # 返回值1: 用于判断新的约束是否加入成功
    # 返回值2: 用于判断新的约束是否是True, False, Unknown
    # 如果没有被添加进去, 其实就不用check了,但是保险一点,也一样check吧
    # 所以综上,凡是unknown的就check以下,否则就不了
    def add_constraint(self, ls):
        # assert self.check() != 'unsat'
        if ls.operands[0].name == ls.operands[1].name:
            return False, 'True'
        if ls.name in self.smt_assumptions:
            return False, 'Unknown' # 这个其实必然是True, 但是保险一点还是返回Unknown
        
        all_constant = 1
        ls.indexing()
        for ls_ent in ls.ent:
            if ls_ent.operands is None:
                self.add_individual_entity(ls_ent)
                if not ls_ent.is_constant:
                    all_constant = 0
        ls2z3_seq = self.ls2z3(ls)
        # 单独判断全是常数的情况
        if all_constant:
            if eval(ls2z3_seq) == False:
                return False, 'False'
            elif eval(ls2z3_seq) == True:
                return False, 'True'
            else:
                assert False, ls2z3_seq
        self.smt_solver.push()
        self.smt_assumptions.append(ls.name)
        self.smt_solver.add_assertion(eval(ls2z3_seq))
        
        return True, 'Unknown' # new ls
    
    def check(self, ):
        return 'unsat' if self.smt_solver.solve() == False else 'sat'
    
    def pop(self,):
        if len(self.smt_assumptions) > 0:
            self.smt_solver.pop()
            self.smt_assumptions.pop()
        
    def ls2z3(self, ls):
        logic_statement_name = re.sub(" ", "", ls.name)
        if logic_statement_name.startswith("BiggerOrEqual"):
            logic_function_name = "BiggerOrEqual"
            logic_statement_name = rm_function_and_brackets(logic_statement_name, logic_function_name)
            two_operands = extract_two_operands(logic_statement_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return r">=".join(two_operands_latex)
        elif logic_statement_name.startswith("Bigger"):
            logic_function_name = "Bigger"
            logic_statement_name = rm_function_and_brackets(logic_statement_name, logic_function_name)
            two_operands = extract_two_operands(logic_statement_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return r">".join(two_operands_latex)
        elif logic_statement_name.startswith("SmallerOrEqual"):
            logic_function_name = "SmallerOrEqual"
            logic_statement_name = rm_function_and_brackets(logic_statement_name, logic_function_name)
            two_operands = extract_two_operands(logic_statement_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return r"<=".join(two_operands_latex)
        elif logic_statement_name.startswith("Smaller"):
            logic_function_name = "Smaller"
            logic_statement_name = rm_function_and_brackets(logic_statement_name, logic_function_name)
            two_operands = extract_two_operands(logic_statement_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return r"<".join(two_operands_latex)
        elif logic_statement_name.startswith("Equivalent"):
            logic_function_name = "Equivalent"
            logic_statement_name = rm_function_and_brackets(logic_statement_name, logic_function_name)
            two_operands = extract_two_operands(logic_statement_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return r"==".join(two_operands_latex)
        else:
            raise NotImplementedError
    
    def entity_name_to_seq_string(self, entity_name):
        if entity_name.startswith("add"):
            outermost_numerical_function = "add"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            two_operands = extract_two_operands(entity_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return "(" + "+".join(two_operands_latex) + ")"
        elif entity_name.startswith("sub"):
            outermost_numerical_function = "sub"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            two_operands = extract_two_operands(entity_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return "(" + "-".join(two_operands_latex) + ")"
        elif entity_name.startswith("mul"):
            outermost_numerical_function = "mul"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            two_operands = extract_two_operands(entity_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return "(" + "*".join(two_operands_latex) + ")"
        elif entity_name.startswith("opp"):
            outermost_numerical_function = "opp"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            return "(-" + self.entity_name_to_seq_string(entity_name) + ")"
        elif entity_name.startswith("sqr"):
            outermost_numerical_function = "sqr"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            return "(" + self.entity_name_to_seq_string(entity_name) + "**2" + ")"
        elif entity_name.startswith("inv"):
            outermost_numerical_function = "inv"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            return "(" + r"1/" + self.entity_name_to_seq_string(entity_name) + ")"
        elif entity_name.startswith("root"):
            outermost_numerical_function = "root"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            return "(" + r"z3.Sqrt(" + self.entity_name_to_seq_string(entity_name) + "))"
        elif entity_name.startswith("pow"):
            outermost_numerical_function = "pow"
            entity_name = rm_function_and_brackets(entity_name, outermost_numerical_function)
            two_operands = extract_two_operands(entity_name)
            two_operands_latex = [self.entity_name_to_seq_string(operand) for operand in two_operands]
            return "(" + "**".join(two_operands_latex) + ")"
        else:
            # Warning: must guarantee the entity is a constant or in the smt_name2var list!
            if entity_name in self.smt_name2var.keys():
                return f"self.smt_name2var['{entity_name}']"
            else:
                return entity_name
    
    def __deepcopy__(self, memo={}):
        result = smt_solver()
        result.smt_name2var = deepcopy(self.smt_name2var)
        result.smt_assumptions = deepcopy(self.smt_assumptions)
        result.smt_solver = deepcopy(self.smt_solver)
        return result
        
    

if __name__ == "__main__":
    s = smt_solver()
    a = Entity(name="a", is_iv=True)
    b = Entity(name="b", is_iv=True)
    one_entity = Entity(name="1", is_constant=True)
    zero_entity = Entity(name="0", is_constant=True)
    a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
    a_and_b_and_one = necessary_numerical_functions["add"].execute_nf([a_and_b, one_entity])
    a_mul_one = necessary_numerical_functions["mul"].execute_nf([a, one_entity])
    final_ent = necessary_numerical_functions["add"].execute_nf([a_mul_one, a_and_b_and_one])
    ls = necessary_logic_functions["BiggerOrEqual"].execute_lf([final_ent, zero_entity])
    ls2 = necessary_logic_functions["Smaller"].execute_lf([final_ent, zero_entity])
    
    # s.add_individual_entity(a)
    # s.add_individual_entity(b)
    # s.add_individual_entity(one_entity)
    # s.add_individual_entity(zero_entity)
    # print(s.smt_solver.num_scopes())
    s.add_constraint(ls)
    # print(s.smt_solver.num_scopes())
    s.add_constraint(ls2)
    # print(s.smt_solver.num_scopes())
    print(s.smt_solver.assertions)
    print(s.smt_assumptions)
    print(s.check())
    s.pop()
    print(s.smt_solver.assertions)
    print(s.smt_assumptions)
    print(s.check())
    s.pop()
    print(s.smt_solver.assertions)
    print(s.smt_assumptions)
    print(s.check())
    
    # print(s.__dict__)
    # print(s.__class__)
    # cls = s.__class__
    # result = cls.__new__(cls)
    # print(result)