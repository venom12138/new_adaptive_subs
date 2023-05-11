from copy import deepcopy

from proof_system.numerical_functions import necessary_numerical_functions
from logic.logic import Entity, LogicStatement
from proof_system.logic_functions import necessary_logic_functions, numpy_logic_functions
from proof_system.numerical_functions import necessary_numerical_functions, numpy_numerical_functions
import random
import numpy as np
random.seed(0)


class EmptyLogicStatement:
    def __init__(self, logic_function, operands, degree=1, premise=None):
        self.logic_function = logic_function
        self.operands = operands
        self.degree = degree
        self.premise = premise
        if logic_function is not None:
            self.update_name()

    def update_name(self):
        def _update_name(entity):
            if entity.operands is not None:
                for ent in entity.operands:
                    _update_name(ent)
                entity.update_name()

        for ent in self.operands:
            _update_name(ent)
        self.name = (self.logic_function.name +
                    " ( " + " , ".join([inp.to_string() for inp in self.operands]) + " )")

# 返回这个logic_statement中所有的符合operator_type的entity
def search_operator_operands_in_gt(logic_statement, operator_type):
    assert operator_type in necessary_numerical_functions
    # Take a logic statement and a given operator type, return all operands of operators of the given type
    # 这个is_structrued是要判断ent的recent_numerical_function是不是operator_type
    operands = [tuple(ent.operands) for ent in logic_statement.ent_dic.values()
                if is_entity(ent) and is_structured(ent, operator_type)]
    operands = set(operands)
    return sorted(operands, key=lambda x: x[0].name)


def substitution(x, y):
    # Given x, y, where ls(x) is the logic statement x is in
    # return ls(y)
    ls_x = x.root
    ls_copy = deepcopy(ls_x)
    x_parent_node = ls_copy.ent_dic[x.parent_index] # 它只改变了parent_node
    for ind, operand in enumerate(x_parent_node.operands):
        if operand.index == x.index:
            replace_ind = ind
            x_parent_node.operands[replace_ind] = deepcopy(y)
        else:
            pass
    ls_copy.indexing()
    ls_copy.update_name()
    return ls_copy

# 找出lhs和rhs中不同的子树：不同意味着numerical_function不同或者operands不同
def sub_tree_diff(ls):
    # Find the subtree that differentiates the lhs and rhs of the logic statement
    lhs, rhs, = deepcopy(ls.operands)
    if lhs.name == rhs.name: # 直接就全相等了
        return [None, None]
    while True:
        if lhs.recent_numerical_function is None or rhs.recent_numerical_function is None:
            return [lhs, rhs]
        if lhs.recent_numerical_function.name != rhs.recent_numerical_function.name:
            return [lhs, rhs] # numerical_function不同，直接就是不同的子树了

        if lhs.recent_numerical_function.input_no == 1: # 如果numerical_function相同，那么就要看它的operands是不是相同
            assert lhs.operands[0].name != rhs.operands[0].name
            lhs = deepcopy(lhs.operands[0])
            rhs = deepcopy(rhs.operands[0])
        elif lhs.recent_numerical_function.input_no == 2:
            if lhs.operands[0].name != rhs.operands[0].name: # 如果operands不同，那么就是不同的子树了
                if lhs.operands[1].name != rhs.operands[1].name:
                    return [lhs, rhs]
                else:
                    lhs = deepcopy(lhs.operands[0]) # 如果只有一个operands不同，那么就继续往下一层
                    rhs = deepcopy(rhs.operands[0])
            elif lhs.operands[1].name != rhs.operands[1].name: # 如果只有一个operands不同，那么就继续往下一层
                lhs = deepcopy(lhs.operands[1])
                rhs = deepcopy(rhs.operands[1])
            else:
                raise AssertionError


def all_different_subtrees(ls):
    # All different subtrees, in the order of parents to children
    lhs, rhs = sub_tree_diff(ls) # 确实，只要找到不同的子树，那所有的爹妈都是不同的子树
    if lhs is None:
        return [(lhs, rhs)]
    all_diff_subtrees = list()
    while is_entity(lhs):
        all_diff_subtrees.append([lhs, rhs])
        lhs = ls.ent_dic[lhs.parent_index]
        rhs = ls.ent_dic[rhs.parent_index]
    return list(reversed(all_diff_subtrees))


def get_entity_coding_from_ls(ls, entity):
    # Use DPS here
    entity_fronts = []
    for i, ent in enumerate(ls.operands):
        if (len(entity.name) == 1 and entity.name in ent.name.split()) or \
                (len(entity.name) != 1 and entity.name in ent.name):
            entity_fronts.append((ent, [i, ]))
    while len(entity_fronts):
        entity_to_search, coding = entity_fronts.pop()
        if entity_to_search == entity:
            return coding

        if entity_to_search.recent_numerical_function is not None:
            for j, ent in enumerate(entity_to_search.operands):
                if (len(entity.name) == 1 and entity.name in ent.name.split()) or \
                        (len(entity.name) != 1 and entity.name in ent.name):
                    further_coding = coding + [j]
                    entity_fronts.append((ent, further_coding))


def get_entity_from_ls_and_coding(ls, coding):
    lhs, rhs, = ls.operands
    ls_root = lhs.root
    current_ent = deepcopy(ls)
    for code in coding:
        if current_ent.operands is None or code >= len(current_ent.operands):
            return False
        current_ent = deepcopy(current_ent.operands[code])
    return ls_root.ent_dic[current_ent.index]


def search_entity_with_name_in_ls(ls, entity_name):
    all_entities = []
    entity_fronts = [ent for ent in ls.operands]
    while len(entity_fronts) > 0:
        entity_to_search = entity_fronts.pop()
        if entity_to_search.name == entity_name:
            all_entities.append(entity_to_search)

        if entity_to_search.recent_numerical_function is not None:
            entity_fronts.extend(entity_to_search.operands)
    return all_entities


def side_of_an_entity(ent):
    ls = ent.root
    current_index = ent.index
    parent_index = ent.parent_index
    while parent_index != 0: # 一直找到根节点
        current_index = parent_index
        parent_index = ls.ent_dic[current_index].parent_index
    if ls.operands[0].index == current_index: # 这个是在判断这个entity是在root节点的左边还是右边
        return "left"
    elif ls.operands[1].index == current_index:
        return "right"
    else:
        raise NotImplementedError


def numerical_problem_axiom_order_valid(steps):
    if len(steps) % 2 == 0:
        return False
    if steps[0]["lemma"].name == "EquivalenceSubstitution":
        return False
    for i, step in enumerate(steps):
        if i != 0:
            if i % 2 == 0:
                if step["lemma"].name != "EquivalenceSubstitution":
                    return False
            elif i % 2 == 1:
                if step["lemma"].name == "EquivalenceSubstitution":
                    return False
            else:
                raise NotImplementedError
    return True


def general_problem_axiom_order_valid(steps):
    for i in range(len(steps) - 1):
        if steps[i]["lemma"].name == "EquivalenceSubstitution" \
                and steps[i + 1]["lemma"].name == "EquivalenceSubstitution":
            return False
    return True


def is_entity(ent):
    if isinstance(ent, Entity):
        return True
    return False


def is_structured(ent, operator_name):
    if ent.recent_numerical_function is not None and ent.recent_numerical_function.name == operator_name:
        return True
    return False

def is_constant(ent):
    if ent.is_constant:
        return True
    return False

def is_ls(ls):
    if isinstance(ls, LogicStatement):
        return True
    return False


def is_empty_ls(ls):
    if isinstance(ls, EmptyLogicStatement):
        return True
    return False


def is_ls_type(ls, type_name):
    if isinstance(ls, LogicStatement) and ls.logic_function.name == type_name:
        return True
    return False


def sample_entity(base_entity, entities, terminal_prob=0.5):
    current_entity = deepcopy(base_entity)
    while random.random() > terminal_prob:
        operator = random.choice(necessary_numerical_functions.values())
        if operator.input_no == 1:
            current_entity = deepcopy(operator.execute_nf([current_entity]))
        elif operator.input_no == 2:
            operands = [current_entity, random.choice(entities)]
            random.shuffle(operands)
            current_entity = deepcopy(operator.execute_nf(operands))
        else:
            raise NotImplementedError
    return current_entity

# input: entity
# output: (entity, opp_num)
# 输入一个entity，判断是不是opp结构+constant，如果是，返回constant和opp的数量，如果不是，返回None
def opposite_simplify(ent):
    if is_entity(ent):
        new_ent = deepcopy(ent)
        opp_num = 0
        while is_structured(new_ent, 'opp'):
            opp_num += 1
            new_ent = new_ent.operands[0]
        if is_constant(new_ent):
            return new_ent, opp_num % 2
        else:
            return None, None
    else:
        return None, None
    
def construct_ls_from_constraint(constraint, entities):
    ls_type = constraint['ls_type']
    structure_constraint = constraint['structure_constraint']
    operands_constraint = constraint['operands_constraint']
    tmp_ls = EmptyLogicStatement(necessary_logic_functions[ls_type], [random.choice(entities),random.choice(entities)])
    # construct a random ls with the same structure as the structure constraint
    for coding, nf_name in structure_constraint.items():
        if necessary_numerical_functions[nf_name].input_no == 1:
            nf = necessary_numerical_functions[nf_name].execute_nf([random.choice(entities)])
        elif necessary_numerical_functions[nf_name].input_no == 2:
            nf = necessary_numerical_functions[nf_name].execute_nf([random.choice(entities), random.choice(entities)])
        cur_ent = tmp_ls
        for code in coding[:-1]:
            cur_ent = cur_ent.operands[code]
        cur_ent.operands[coding[-1]] = nf
    
    # construct a ls with the same operands as the operands constraint
    for name, coding in operands_constraint.items():
        ent = Entity(name=name, is_constant=True)
        cur_ent = tmp_ls
        for code in coding[:-1]:
            cur_ent = cur_ent.operands[code]
        cur_ent.operands[coding[-1]] = ent
    final_ls = necessary_logic_functions[ls_type].execute_lf([tmp_ls.operands[0], tmp_ls.operands[1]])
    return final_ls

def is_all_operands_constant(ls,):
    all_ents = [ls.operands[0], ls.operands[1]]
    constant_status = []
    while len(all_ents) > 0:
        ent = all_ents.pop(0)
        if ent.operands is not None:
            all_ents.extend(ent.operands)
        else:
            constant_status.append(ent.is_constant)
    if all(constant_status): # 如果所有的entity都是constant
        return True
    else:
        return False # 但凡有一个不是
    
def is_either_side_operands_constant(ls,):
    left_side_ents = [ls.operands[0], ]
    right_side_ents = [ls.operands[1], ]
    left_constant_status = []
    right_constant_status = []
    while len(left_side_ents) > 0:
        ent = left_side_ents.pop(0)
        if ent.operands is not None:
            left_side_ents.extend(ent.operands)
        else:
            left_constant_status.append(ent.is_constant)
    
    while len(right_side_ents) > 0:
        ent = right_side_ents.pop(0)
        if ent.operands is not None:
            right_side_ents.extend(ent.operands)
        else:
            right_constant_status.append(ent.is_constant)
    
    if all(left_side_ents) or all(right_side_ents): # 如果有一个side的entity都是constant
        return True
    else:
        return False # 两边都不是

def is_side_operands_constant(ls,side):
    assert side in [0, 1]
    side_ents = [ls.operands[side],]
    constant_status = []
    while len(side_ents) > 0:
        ent = side_ents.pop(0)
        if ent.operands is not None:
            side_ents.extend(ent.operands)
        else:
            constant_status.append(ent.is_constant)
    
    if all(side_ents): # 如果有一个side的entity都是constant
        return True
    else:
        return False # 两边都不是

def numerical_compute_entity(entity):
    assert is_entity(entity)
    if entity.is_constant:
        return int(entity.name)
    elif (entity.recent_numerical_function is not None) and (entity.operands is not None):
        if entity.recent_numerical_function.input_no == 1:
            return numpy_numerical_functions[entity.recent_numerical_function.name](numerical_compute_entity(entity.operands[0]))
        elif entity.recent_numerical_function.input_no == 2:
            if entity.recent_numerical_function.name == 'pow':
                return numpy_numerical_functions[entity.recent_numerical_function.name](float(numerical_compute_entity(entity.operands[0])), \
                            numerical_compute_entity(entity.operands[1]))
            return numpy_numerical_functions[entity.recent_numerical_function.name](numerical_compute_entity(entity.operands[0]), \
                            numerical_compute_entity(entity.operands[1]))
        else:
            raise NotImplementedError
    else:
        assert False

# 假定已经check过全部都是constant
def numerical_compute_logic_statement(logic_statement):
    operand1 = numerical_compute_entity(logic_statement.operands[0])
    operand2 = numerical_compute_entity(logic_statement.operands[1])
    if np.isnan(operand1) or np.isnan(operand2):
        return False
    return numpy_logic_functions[logic_statement.logic_function.name](operand1, operand2)


def sample_ls(problem_graph, ls_list, prob):
    if np.random.rand() < prob:
        ls_name_list = [ls.name for ls in ls_list]
        effective_node_list = []
        for node in problem_graph.nodes:
            if node.name in ls_name_list:
                effective_node_list.append(node)
        if len(effective_node_list) == 0:
            return random.choice(ls_list)
        effective_node_list.sort(key=lambda x: x.ancesters_num, reverse=True)
        idx = ls_name_list.index(effective_node_list[0].name)
        return ls_list[idx]
    else:
        return random.choice(ls_list)

if __name__ == "__main__":
    a = Entity(name="a", is_iv=True)
    b = Entity(name="b", is_iv=True)
    one_entity = Entity(name="1", is_constant=True)
    zero_entity = Entity(name="0", is_constant=True)
    a_and_b = necessary_numerical_functions["add"].execute_nf([a, b])
    a_and_b_and_one = necessary_numerical_functions["add"].execute_nf([a_and_b, one_entity])
    a_mul_one = necessary_numerical_functions["mul"].execute_nf([a, one_entity])
    final_ent = necessary_numerical_functions["add"].execute_nf([a_mul_one, a_and_b_and_one])
    ls = necessary_logic_functions["BiggerOrEqual"].execute_lf([a_and_b_and_one, zero_entity])
    ls2 = necessary_logic_functions["Smaller"].execute_lf([final_ent, zero_entity])
    ls3 = necessary_logic_functions["Smaller"].execute_lf([a_and_b, zero_entity])
    ls_list = [ls, ls2, ls3]
    print(ls_list)
    ls_list.sort(key=lambda ls: len(ls.name), reverse=True)
    print(ls_list)