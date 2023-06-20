import random
import string
import time
import sys
sys.path.append("./third_party/INT")
sys.path.insert(0, "/additional_packages")
sys.path.append("./third_party")
import gin
import torch
from joblib import Parallel, delayed
import numpy as np
import os
from envs.int.theorem_prover_env import TheoremProverEnv
from metric_logging import log_text
from third_party.INT.proof_system.all_axioms import axiom_sets
from supervised.int.int_hacking import sample_axiom_order, \
    generate_problem__single_trial
# from third_party.INT.data_generation.multi_path_generate_problems import generate_problem
from utils import storage
from supervised.int.gen_subgoal_data import set_rnd_seed_and_generate_problem
import joblib
from tqdm import tqdm
from copy import deepcopy

def generate_eval_problems(save_path, start_chunk=0, n_proofs=1e6, n_workers=20, num_proof_per_chunk=1000,
                            proof_length_list=[4,8,12,16,20,24], seed=None, max_length_mode=True):
    num_chunks = n_proofs // num_proof_per_chunk
    np.random.seed(seed)
    if seed is not None:
        torch.manual_seed(seed)
    problems_dict = {}
    for proof_length in proof_length_list:
        problems_dict[proof_length] = []
    
    cur_proof_length_list = deepcopy(proof_length_list)
    while True:
        for cur_proof_length in reversed(cur_proof_length_list):
            if len(cur_proof_length_list) == 0:
                break
            rng = np.random.default_rng(np.random.randint(low=0, high=2**32, size=1)[0])
            
            seeds = rng.integers(low=0, high=2**63, size=300)
            # print(seeds)
            problems = Parallel(n_jobs=n_workers, verbose=9)(
                    delayed(set_rnd_seed_and_generate_problem)(
                        seed=seed,
                        proof_length=cur_proof_length+5,
                        available_axioms=axiom_sets["ordered_field"],
                        max_length_mode=max_length_mode,
                    ) for seed in seeds)
            
            for problem in problems:
                print(f"problem length:{len(problem)}")
                if len(problem) in cur_proof_length_list:
                    problems_dict[len(problem)].append(problem)
                    if len(problems_dict[len(problem)]) >= n_proofs:
                        cur_proof_length_list.remove(len(problem))
            print(f"problems num:{[len(problems_dict[proof_length]) for proof_length in proof_length_list]}")
        if len(cur_proof_length_list) == 0:
            break
    
    for length, problems in problems_dict.items():
        os.makedirs(f'{save_path}/length_{length}', exist_ok=True)
        cur_chunk = start_chunk
        while True:
            joblib.dump(problems[:num_proof_per_chunk], filename=f'{save_path}/length_{length}/chunk_{cur_chunk:08d}')
            problems = problems[num_proof_per_chunk:]
            if len(problems) <= 0:
                break
            cur_chunk += 1
        # joblib.dump(problems, filename=f'{save_path}/chunk_{cur_chunk:08d}')

if __name__ == '__main__':
    generate_eval_problems(save_path='./eval_data', start_chunk=0, n_proofs=100, n_workers=60, 
                            num_proof_per_chunk=100, proof_length_list=[5,8,13,16,20], seed=452763)