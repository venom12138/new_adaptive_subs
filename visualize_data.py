import random
import string
import time
import sys
sys.path.append("./third_party/INT")
sys.path.append("./third_party")
import gin
import torch
from joblib import Parallel, delayed
import numpy as np

from envs.int.theorem_prover_env import TheoremProverEnv
from metric_logging import log_text
from third_party.INT.proof_system.all_axioms import axiom_sets
from third_party.INT.visualization.seq_parse import my_logic_statement_name_to_seq_string
from supervised.int.int_hacking import sample_axiom_order, \
    generate_problem__single_trial
# from third_party.INT.data_generation.multi_path_generate_problems import generate_problem
from utils import storage

problem_loader = storage.LongListLoader('/home/lxj/venom/new_adaptive_subs/data', 0)
problems = problem_loader.load(1000)
problem_length_dict = {}
for length in range(3,20):
    problem_length_dict[length] = 0
for problem in problems:
    assert len(problem) in problem_length_dict.keys()
    problem_length_dict[len(problem)] += 1
    # print(f"problem_length:{len(problem)}")
    # print('-----------------')
    # print(f"condition:{[my_logic_statement_name_to_seq_string(gt.name) for gt in problem[0]['observation']['ground_truth']]}")
    # print(f"objective:{[my_logic_statement_name_to_seq_string(gt.name) for gt in problem[0]['observation']['objectives']]}")
print(problem_length_dict)