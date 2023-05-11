""" Some functions from INT modified for our needs.

The functions here are on purpose minimal modifications of original INT
functions, without additional refactoring or stylistic changes.
"""
import random

from third_party.INT.data_generation.combos_and_orders import (
    get_combo_order_info, randomize_one_axiom_order,
    generate_order_from_combination
)
from third_party.INT.data_generation.multi_path_generate_problems import \
    get_a_forward_problem
from third_party.INT.data_generation.utils import (
    initialize_prover, generate_valid_steps, 
    steps_valid
)
from third_party.INT.data_generation.graph_forward2backward import graph_forward_to_backward
import gin

def generate_problem__single_trial(num_axioms, train_test, **kwargs):
    """
    Based on INT::generate_problem(), tries to generate problem once. The
    problem with original function is that it needs to get large set of
    combinations/orders as input, since some of them might be invalid.
    """

    avoid_objective_names = kwargs.get("avoid_objective_names", [])
    length = kwargs.get("length", None) # max length mode not specify length
    if length is None: # max length mode
        length = 0
    # Get combos or orders ready
    use_combos, use_orders, k_combos, kl_orders, available_indices = \
        get_combo_order_info(num_axioms, train_test, **kwargs)
    # Initialize the atomic entities and the proof
    atom_ents, prover = initialize_prover(**kwargs)

    done = False
    returned_steps = None
    for _ in [0]:
        axiom_order = randomize_one_axiom_order(use_combos, use_orders, k_combos, kl_orders, available_indices)
        if len(axiom_order) < length:
            return None

        result = get_a_forward_problem(atom_ents, prover, axiom_order, **kwargs)
        
        if result is None:
            return None
        
        conditions, objectives, compact_proof_graph = result
        steps = graph_forward_to_backward(compact_proof_graph)
        
        if steps == None or steps == False:
            return None
        try:
            # Convert the proof to backward and validate it
            returned_steps = generate_valid_steps(steps)
            if returned_steps == False:
                return None
        except TypeError:
            return None
        
        if returned_steps[0]["observation"]["objectives"][0].name in avoid_objective_names:
            return None
        # specify length mode
        if length > 0 and len(returned_steps) != length:
            return None
        if len(returned_steps) < 4:
            return None
        # compact_proof_graph.visualize()
        done = True
        steps_valid(returned_steps)

    if not done:
        returned_steps = None
    return returned_steps

# @gin.configurable
# order_length is different from proof_length in new_INT
# order_length should be specified in above level
def sample_axiom_order(order_length, available_axioms):
    # based on INT::generate_combinations_and_orders()
    order = None
    while True:
        combination = random.sample(
            list(available_axioms.keys()),
            k=min(order_length, len(available_axioms))
        )
        try:
            order = generate_order_from_combination(
                combination, order_length, use_tuple=True)
        except IndexError:
            continue
        break
    return order
