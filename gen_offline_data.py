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

from envs.int.theorem_prover_env import TheoremProverEnv
from metric_logging import log_text
from third_party.INT.proof_system.all_axioms import axiom_sets
from supervised.int.int_hacking import sample_axiom_order, \
    generate_problem__single_trial
# from third_party.INT.data_generation.multi_path_generate_problems import generate_problem
from utils import storage
from supervised.int.gen_subgoal_data import set_rnd_seed_and_generate_problem
import joblib

def generate_offline_problems(save_path, n_proofs=1e6, n_workers=20, num_proof_per_chunk=1000,
                            proof_length=15, seed=None, max_length_mode=True):
    num_chunks = n_proofs // num_proof_per_chunk
    np.random.seed(seed)
    if seed is not None:
        torch.manual_seed(seed)
    for cur_chunk in range(num_chunks):
        problems = []
        rng = np.random.default_rng(np.random.randint(low=0, high=2**32, size=1)[0])
        seeds = rng.integers(low=0, high=2**63, size=num_proof_per_chunk)
        problems.extend(
            Parallel(n_jobs=n_workers, verbose=9)(
                delayed(set_rnd_seed_and_generate_problem)(
                    seed=seed,
                    proof_length=proof_length,
                    available_axioms=axiom_sets["ordered_field"],
                    max_length_mode=max_length_mode,
                ) for seed in seeds)
        )
        joblib.dump(problems, filename=f'{save_path}/chunk_{cur_chunk:08d}')

if __name__ == '__main__':
    generate_offline_problems(save_path='./data', n_proofs=1000, n_workers=20, num_proof_per_chunk=200,)