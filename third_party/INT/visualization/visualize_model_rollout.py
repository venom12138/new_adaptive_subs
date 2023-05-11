import json
import os
import pickle
import random
import numpy as np
from datetime import datetime
from time import time

import torch
import torch.optim as optim
import torch.utils.data as data_handler
import argparse
from algos.lib.obs import nodename2index, thm2index, batch_process
from data_generation.multi_path_generate_problems import generate_multiple_problems
from data_generation.utils import Dataset
from visualization.latex_parse import logic_statement_to_latex, parse

from algos.lib.envs import make_thm_env

timestamp = str(datetime.fromtimestamp(time())).replace(" ", "_").replace(":", "_").replace("-", "_").replace(".", "_")
parser = argparse.ArgumentParser(description='ThmProving')
# datasets
parser.add_argument("-d", "--path_to_data", required=False, type=str,
                    help="what data algos to use")
parser.add_argument("-trs", "--train_sets", required=False, type=str, nargs="+", default=["k=10_l=10"])
parser.add_argument("-tes", "--test_sets", required=False, type=str, nargs="+", default=["k=10_l=10"])
parser.add_argument("-o", "--obs_mode", required=False, type=str, default="geometric",
                    help="which mode of observation to use")
parser.add_argument("-np", '--num_probs', required=False, type=int, default=1000,
                    help="number of problems per combination")
parser.add_argument("-es", "--evaluation_size", required=False, type=int, default=256,
                    help="how many points to validate on")
parser.add_argument("-nvp", "--num_val_probs", required=False, type=int, default=100,
                    help="how many points to validate on")
parser.add_argument("-ntp", "--num_test_probs", required=False, type=int, default=20,
                    help="how many points to test on")
parser.add_argument("-tg", "--transform_gt", action='store_true',
                    help="whether to use transform_gt")
parser.add_argument("--online", required=False, action='store_true', default=True)
parser.add_argument('-cp', "--combo_path", required=False, type=str,
                    default="data/benchmark/ordered_field")
parser.add_argument("-oog", "--online_order_generation", action='store_true',
                    help="whether to use the axiom combinations to generate orders on the fly")
parser.add_argument("-nooc", "--num_order_or_combo", required=False, type=int, default=-1,
                    help="number of orders or combos to use")

# training settings
parser.add_argument("--cuda", action='store_true',
                    help="how many total updates")
parser.add_argument("-du", "--dump", required=False, type=str,
                    help="what dumping algos to use")
parser.add_argument("-rd", "--resume_dir", required=False, default="", type=str,
                    help="what custom algos to use")
parser.add_argument("-pr", "--pretrain_dir", required=False, default="", type=str,
                    help="what algos to load pretrain model")
parser.add_argument("-fp", "--fix_policy", action='store_true',
                    help="whether to fix policy and train baseline for the first part of training")
parser.add_argument("-epr", "--epoch_per_record", required=False, type=int, default=1,
                    help="how many epochs per record")
parser.add_argument("-epcr", "--epoch_per_case_record", required=False, type=int, default=10,
                    help="how many epochs per record for right and wrong cases")
parser.add_argument("-epod", "--epochs_per_online_dataset", required=False, type=int, default=10)
parser.add_argument("-e", "--epoch", required=False, type=int, default=100000,
                    help="how many epochs")
parser.add_argument("-u", "--updates", required=False, type=int, default=200000,
                    help="how many total updates")
parser.add_argument("--time_limit", required=False, type=int, default=20)
parser.add_argument("--seed", required=False, type=int, default=0)

# optimization hps
parser.add_argument('--lr', type=float, default=1e-5, help='learning rate (default: 7e-4)')
parser.add_argument("-bs", "--batch_size", required=False, type=int, default=32,
                    help="what batch size to use")
parser.add_argument("-le", "--lemma_cost", required=False, type=float, default=1.0,
                    help="lemma cost")
parser.add_argument("-ent", "--entity_cost", required=False, type=float, default=1.0,
                    help="entity cost")
parser.add_argument("-dr", "--dropout_rate", required=False, type=float, default=0.0,
                    help="dropout rate")
parser.add_argument("-gdr", "--gat_dropout_rate", required=False, type=float, default=0.0,
                    help="dropout rate in gat")

# neural architecture hps
parser.add_argument("-hi", "--hidden", required=False, default=6, type=int,
                    help="how many hidden layers of nn")
parser.add_argument("-hd", "--hidden_dim", required=False, type=int, default=512,
                    help="what state dimension to use")
parser.add_argument("-gt", "--gnn_type", required=False, type=str, default="GIN",
                    help="what type of GNN to use")
parser.add_argument("-atten", "--atten_type", type=int, required=False, default=0,
                    help="attention type")
parser.add_argument("-ah", "--attention_heads", type=int, required=False, default=8,
                    help="attention heads")
parser.add_argument("-n", "--norm", required=False, type=str, default=None,
                    help="what norm to use")
# TODO: change this boolean argument to be false
parser.add_argument("-cgo", "--combined_gt_obj", action='store_false',
                    help="whether to use a combined gt and obj encoder")
parser.add_argument("-bag", "--bag_of_words", action='store_true',
                    help="whether to use bag of words model")

# Environment setting
parser.add_argument("-m", "--mode", required=False, default="solve", type=str,
                    help="whether to discover or to solve")
parser.add_argument("--verbo", required=False, action='store_true',
                    help="whether to use verbo")
parser.add_argument("--degree", required=False, type=int, default=0,
                    help="the degree of the starting entities")

# RL specific setting

parser.add_argument('--eval_interval', type=int, default=None,
                    help='eval interval, one eval per n updates (default: None)')
parser.add_argument('--algo', default='a2c', help='algorithm to use: a2c | ppo | acktr')
parser.add_argument('--gail', action='store_true', default=False,
                    help='do imitation learning with gail')
parser.add_argument('--gail-experts-dir', default='./gail_experts',
                    help='algos that contains expert demonstrations for gail')
parser.add_argument('--gail-batch-size', type=int, default=128,
                    help='gail batch size (default: 128)')
parser.add_argument('--gail-epoch', type=int, default=5, help='gail epochs (default: 5)')
parser.add_argument('--eps', type=float, default=1e-5,
                    help='RMSprop optimizer epsilon (default: 1e-5)')
parser.add_argument('--alpha', type=float, default=0.99,
                    help='RMSprop optimizer apha (default: 0.99)')
parser.add_argument('--gamma', type=float, default=0.99,
                    help='discount factor for rewards (default: 0.99)')
parser.add_argument('--use-gae', action='store_true', default=False,
                    help='use generalized advantage estimation')
parser.add_argument('--gae-lambda', type=float, default=0.95,
                    help='gae lambda parameter (default: 0.95)')
parser.add_argument('--entropy-coef', type=float, default=0.01,
                    help='entropy term coefficient (default: 0.01)')
parser.add_argument('--value-loss-coef', type=float, default=0.5,
                    help='value loss coefficient (default: 0.5)')
parser.add_argument('--max-grad-norm', type=float, default=0.5,
                    help='max norm of gradients (default: 0.5)')
parser.add_argument('--cuda-deterministic', action='store_true', default=False,
                    help="sets flags for determinism when using CUDA (potentially slow!)")
parser.add_argument("--num_processes", required=False, type=int, default=5,
                    help="the number of parallel processes")
parser.add_argument('--num_steps', type=int, default=4,
                    help='number of forward steps in A2C (default: 4)')
parser.add_argument('--ppo-epoch', type=int, default=4,
                    help='number of ppo epochs (default: 4)')
parser.add_argument('--num-mini-batch', type=int, default=32,
                    help='number of batches for ppo (default: 32)')
parser.add_argument('--clip-param', type=float, default=0.2,
                    help='ppo clip parameter (default: 0.2)')
parser.add_argument('--log-interval', type=int, default=10,
                    help='log interval, one l per n updates (default: 10)')
parser.add_argument('--save-interval', type=int, default=100,
                    help='save interval, one s  per n updates (default: 100)')
parser.add_argument('--eval-interval', type=int, default=None,
                    help='eval interval, one e  per n updates (default: None)')
parser.add_argument('--num-env-steps', type=int, default=10e6,
                    help='number of environment steps to train (default: 10e6)')
parser.add_argument('--env-name', default='PongNoFrameskip-v4',
                    help='environment to train on (default: PongNoFrameskip-v4)')
parser.add_argument('--saving_dir', default='/tmp/gym/',
                    help='algos to save agent logs (default: /tmp/gym)')
parser.add_argument('--save-dir', default='./trained_models/',
                    help='algos to save agent logs (default: ./trained_models/)')
parser.add_argument('--no-cuda', action='store_true', default=False,
                    help='disables CUDA training')
parser.add_argument('--use-proper-time-limits', action='store_true', default=False,
                    help='compute returns taking into account time limits')
parser.add_argument('--recurrent-policy', action='store_true', default=False,
                    help='use a recurrent policy')
parser.add_argument('--use-linear-lr-decay', action='store_true', default=False,
                    help='use a linear schedule on the learning rate')

args = parser.parse_args()

args.use_gpu = args.cuda and torch.cuda.is_available()
device = torch.device("cuda" if args.use_gpu else "cpu")

if args.num_order_or_combo < 0:
    args.num_order_or_combo = None

dgl = (args.obs_mode == "dgl")
bow = args.bag_of_words
print(args.transform_gt)
if dgl and (not bow):
    from algos.model.thm_model_dgl import ThmNet
elif bow and (not dgl):
    from algos.model.thm_model import ThmNet
elif (not bow) and (not dgl):
    from algos.model.thm_model import ThmNet
else:
    raise AssertionError

torch.manual_seed(args.seed)
if args.use_gpu:
    torch.cuda.manual_seed_all(0)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False
    os.environ['PYTHONHASHSEED'] = str(0)
random.seed(args.seed)
np.random.seed(args.seed)

def load_checkpoint(model, optimizer, filename):
    checkpoint = torch.load(filename)
    model.load_state_dict(checkpoint['model'])
    optimizer.load_state_dict(checkpoint['optimizer'])
    return checkpoint['extra']

def load_data(data_dir, mode="train"):
    file_name = os.path.join(data_dir, '{}.pkl'.format(mode))
    with open(file_name, 'rb') as f:
        dataset = pickle.load(f)
    return dataset

def load_optimizer(model):
    return optim.Adam(model.parameters(), lr=args.lr)

def load_all_data(train_dirs, test_dirs):
    train_dataset = Dataset([])
    val_dataset = Dataset([])
    train_first_dataset = Dataset([])
    val_first_dataset = Dataset([])
    for train_dir in train_dirs:
        train_ds = load_data(train_dir, mode="train")
        train_dataset.merge(train_ds)
        val_ds = load_data(train_dir, mode="val")
        val_dataset.merge(val_ds)
        train_first_ds = load_data(train_dir, mode="train_first")
        train_first_dataset.merge(train_first_ds)
        val_first_ds = load_data(train_dir, mode="val_first")
        val_first_dataset.merge(val_first_ds)

    test_dataset = Dataset([])
    test_first_dataset = Dataset([])
    for test_dir in test_dirs:
        test_ds = load_data(test_dir, mode="test")
        test_dataset.merge(test_ds)
        test_first_ds = load_data(test_dir, mode="test_first")
        test_first_dataset.merge(test_first_ds)
    return {
        "train": train_dataset,
        "train_first": train_first_dataset,
        "val": val_dataset,
        "val_first": val_first_dataset,
        "test": test_dataset,
        "test_first": test_first_dataset
    }

def load_model():
    options = dict(
        num_nodes=len(nodename2index),
        num_lemmas=len(thm2index),
        hidden_dim=args.hidden_dim,
        gnn_type=args.gnn_type,
        combined_gt_obj=args.combined_gt_obj,
        attention_type=args.atten_type,
        hidden_layers=args.hidden,
        norm=args.norm,
        entity_cost=args.entity_cost,
        lemma_cost=args.lemma_cost,
        cuda=args.use_gpu,
        attention_heads=args.attention_heads,
        gat_dropout_rate=args.gat_dropout_rate,
        dropout_rate=args.dropout_rate,
    )
    return ThmNet(**options)



def eval_agent(agent, env_config, log_dir=None):
    # Evaluate policy rollout success rates and record right and wrong cases
    # TODO: get multi-processing working

    env = make_thm_env(env_config, log_dir=log_dir)()

    actor_critic = agent
    timestamp = str(datetime.fromtimestamp(time())).replace(" ", "_").replace(":", "_").replace("-", "_").replace(".", "_")
    output_file = f'./visuals/{timestamp}.txt'
    obs = env.reset(index=0)
    # print(f"obs: {env.env.proof.parser.observation_to_source(env.env.proof.get_observation())}")
    # with open(output_file, '+a') as of:
    #     of.write(f"obs: {env.env.proof.parser.observation_to_source(env.env.proof.get_observation())}\n")
    successes = []
    right_cases = []
    wrong_cases = []
    previous_steps = []
    prob_index = 0
    num_steps = []
    
    while not env.eval_finish:
        try:
            # Sample actions
            with torch.no_grad():
                action, value = actor_critic.forward([obs])
                # action, value = actor_critic.compute_action(obs)
                # Obser reward and next obs
            
            action2show = env.env._get_action(action[0])
            # print(f"action: {action2show[0].name, [parse(operand.name) for operand in action2show[1]]}") 
            obs, reward, done, infos = env.step(action[0])
            print(f"obs: {infos['gt']} to {infos['obj']}")
            print(f"action:{infos['lemma'], infos['input_entities']}")
            print(f'reward:{reward}')
            
            with open(output_file, '+a') as of:
                of.write(f"obs: {infos['gt']} to {infos['obj']}\n")
                of.write(f"action:{infos['lemma'], infos['input_entities']}\n")
                of.write(f'reward:{reward}\n')
            
        except RuntimeError:
            reward, done, infos = 0, True, "CUDA OUT OF MEMORY"
        # obs, reward, done, infos = env.step(action)
        previous_steps.append(infos)
        if done:
            prob_index += 1
            successes.extend([reward])
            if reward:
                right_cases.append(previous_steps)
                print("prob {} success!".format(prob_index))
                with open(output_file, '+a') as of:
                    of.write("prob {} success!\n".format(prob_index))
            else:
                print("prob {} fail!".format(prob_index))
                with open(output_file, '+a') as of:
                    of.write("prob {} fail!\n".format(prob_index))
                
                wrong_cases.append(previous_steps)
            num_steps.append(len(previous_steps))
            obs = env.reset()
            with open(output_file, '+a') as of:
                of.write("\nnew question:\n")
            print("\nnew question:")
            # print(f"obs: {env.env.proof.parser.observation_to_source(env.env.proof.get_observation())}")
            # with open(output_file, '+a') as of:
            #     of.write(f"obs: {env.env.proof.parser.observation_to_source(env.env.proof.get_observation())}\n")
            # if done:
            #     successes.append(reward)
            previous_steps = []
            
    return np.mean(successes), wrong_cases, right_cases, np.mean(num_steps)

# Test every epoch
def test_rollout(model, test_dataset, whole_dataset=False):
    model.eval()
    if whole_dataset:
        test_starting_points = test_dataset.trajectories
    else:
        indices = range(len(test_dataset))
        test_starting_points = [test_dataset.trajectories[index]
                                for index in random.sample(indices, k=args.num_test_probs)]
    env_config = {
        "mode": "eval",
        "eval_dataset": test_starting_points,
        "online": False,
        "batch_eval": False,
        "verbo": True,
        "obs_mode": args.obs_mode,
        "bag_of_words": args.bag_of_words,
        "time_limit": args.time_limit,
        "degree": args.degree
    }
    success_rate, wrong_cases, success_cases, avg_num_steps = \
        eval_agent(model, env_config=env_config)

    model.train()
    return success_rate, wrong_cases, success_cases, avg_num_steps

if __name__ == "__main__":
    model = load_model().cuda()
    optimizer = load_optimizer(model)
    file_name = '/home/venom/projects/Automated_Theorem_Proving/new_INT/data/pt_models/best_epoch.pth'
    load_checkpoint(model, optimizer, file_name)
    kl_dict = json.load(open(os.path.join(args.combo_path, "orders.json"), "r"))
    train_first_dataset = Dataset([])
    kl = args.train_sets[0]
    k = int(kl.split("_")[0].split('=')[-1])
    l = int(kl.split("_")[1].split('=')[-1])
    keyword_arguments = {"orders": kl_dict}
    one_piece_of_data, _ = generate_multiple_problems(num_axioms=k, max_length=0, length=l, num_probs=args.num_test_probs,
                                                        train_test="train", backwards=True,
                                                        transform_gt=args.transform_gt, degree=args.degree,
                                                        num_order_or_combo=args.num_order_or_combo,
                                                        **keyword_arguments)
    # one_piece_of_data = one_piece_of_data[f"k={k}l={l}"]
    train_first_dataset.merge(one_piece_of_data["all_first"][f"k={k}l={l}"])
    train_first_success_rate, train_first_wrong_case, train_first_right_case, train_first_avg_proof_length = \
                test_rollout(model, train_first_dataset)