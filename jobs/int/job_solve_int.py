import pickle
import time
from copy import deepcopy

from joblib import Parallel, delayed

from jobs.core import Job
from metric_logging import log_scalar, log_scalar_metrics, MetricsAccumulator, log_text
from supervised.int.gen_subgoal_data import generate_problems

from third_party.INT.visualization.seq_parse import logic_statement_to_seq_string, entity_to_seq_string
import torch
import joblib
import warnings
warnings.filterwarnings("ignore", category=UserWarning)

def solve_problem(solver, input_state, device=None):
    time_s = time.time()
    solver.construct_networks(device)
    solution, tree_metrics, root, trajectory_actions, additional_info, goals_for_verification = solver.solve(input_state)
    time_solving = time.time() - time_s
    return dict(
        solution=solution,
        tree_metrics=tree_metrics,
        root=root,
        trajectory_actions=trajectory_actions,
        time_solving=time_solving,
        input_problem=deepcopy(input_state),
        additional_info=additional_info,
        goals_for_verification=goals_for_verification
    )


class JobSolveINT(Job):
    def __init__(self,
                 solver_class,
                 n_jobs,
                 n_parallel_workers,
                 batch_size,
                 budget_checkpoints=None,
                 real_budget_checkpoints=None,
                 log_solutions_limit=100,
                 job_range=None,
                 collect_solutions=None
                 ):

        self.solver_class = solver_class
        self.n_jobs = n_jobs
        self.n_parallel_workers = n_parallel_workers
        self.batch_size = batch_size
        self.budget_checkpoints = budget_checkpoints
        self.real_budget_checkpoints = real_budget_checkpoints
        self.log_solutions_limit = log_solutions_limit
        self.job_range = job_range
        self.collect_solution = collect_solutions

        self.solved_stats = MetricsAccumulator()
        self.experiment_stats = MetricsAccumulator()
        self.calls_stats = MetricsAccumulator()
        self.distance_stats = MetricsAccumulator()

        self.verifications = dict()

        self.logged_solutions = 0

        if self.collect_solution is not None:
            self.collection = {}

    def execute(self):
        solver = self.solver_class()
        # solver.construct_networks()
        batch_jobs = 100
        batch_goals = 1000
        devices = torch.cuda.device_count()
        devices = [torch.device(f'cuda:{i}') for i in range(devices)]
        positive_goals = []
        negative_goals = []
        positive_chunk_num = 125
        negative_chunk_num = 339
        if self.n_jobs % batch_jobs != 0:
            epochs = self.n_jobs // batch_jobs + 1
        else:
            epochs = self.n_jobs // batch_jobs
        for i in range(epochs):
            total_time_start = time.time()
            if i == epochs - 1 and self.n_jobs % batch_jobs != 0:
                jobs_to_do = self.n_jobs - i * batch_jobs
            else:
                jobs_to_do = min(batch_jobs, self.n_jobs)
            jobs_done = 0
            batch_num = 0
            proofs_to_solve = generate_problems(jobs_to_do)
            while jobs_to_do > 0:
                jobs_in_batch = min(jobs_to_do, self.batch_size)
                boards_to_solve_in_batch = proofs_to_solve[jobs_done:jobs_done + jobs_in_batch]

                results = Parallel(n_jobs=self.n_parallel_workers, verbose=100)(
                    delayed(solve_problem)(solver, input_problem[0],) for input_problem in boards_to_solve_in_batch
                )
                batch_positive_goals, batch_negative_goals = self.save_data_for_verificator(results)
                positive_goals.extend(batch_positive_goals)
                negative_goals.extend(batch_negative_goals)
                while len(positive_goals) > batch_goals:
                    joblib.dump(positive_goals, f'output_verificator/positive_chunk_{positive_chunk_num:08d}')
                    positive_chunk_num += 1
                    positive_goals = positive_goals[batch_goals:]
                while len(negative_goals) > batch_goals:
                    joblib.dump(negative_goals, f'output_verificator/negative_chunk_{negative_chunk_num:08d}')
                    negative_chunk_num += 1
                    negative_goals = negative_goals[batch_goals:]
                print(f"positive_goals:{len(positive_goals)}, negative_goals:{len(negative_goals)}")
                self.log_results(results, jobs_done)
                jobs_done += jobs_in_batch
                jobs_to_do -= jobs_in_batch
                batch_num += 1

            for metric, value in self.solved_stats.return_scalars().items():
                log_text('summary', f'{metric},  {value}')
            log_text('summary', f'Finished time {i}, {time.time() - total_time_start}')
            print(f'Finished time {i}, {time.time() - total_time_start}')
    
    def save_data_for_verificator(self, results):
        n_logs = len(results)
        positive_goals = []
        negative_goals = []
        for log_num, result in enumerate(results):
            batch_positive_goals, batch_negative_goals = result.pop('goals_for_verification')
            positive_goals.extend(batch_positive_goals)
            negative_goals.extend(batch_negative_goals)
        return positive_goals, negative_goals
    
    def log_results(self, results, step):
        n_logs = len(results)
        for log_num, result in enumerate(results):
            log_scalar_metrics('tree', step+log_num, result['tree_metrics'])
            if self.logged_solutions < self.log_solutions_limit:
                self.log_solution(result['solution'], result['trajectory_actions'], result['input_problem'], step+log_num)
            solved = result['solution'] is not None
            self.experiment_stats.log_metric_to_accumulate('tested', 1)
            log_scalar_metrics('problems', step+log_num, self.experiment_stats.return_scalars())
            log_scalar('time_solving', step + log_num, result['time_solving'])

            if solved:
                self.solved_stats.log_metric_to_average('rate/all', 1)
                self.solved_stats.log_metric_to_accumulate('problems', 1)
                log_scalar('solution', step + log_num, 1)
                log_scalar('solution/length', step + log_num, len(result['trajectory_actions']))
                # assert False
                trajectory_actions = [str(action) for action in result['trajectory_actions']]
                trajectory = ', '.join(trajectory_actions)
                log_text('trajectory_actions', f'{step + log_num}: {trajectory}', False)
                log_scalar('solution/n_subgoals', step + log_num, len(result['solution']))

                # subgoal distances
                path = list(reversed(result['additional_info']['subgoal_distances']))
                if len(path) >= 1:
                    for id in [0, 1, -1, -2]:
                        log_scalar(f'solution/distances/step nb. {id}', step + log_num, path[id])
                        self.distance_stats.log_metric_to_average(f'avg step nb. {id}', path[id])
            else:
                self.solved_stats.log_metric_to_average('rate/all', 0)
                self.solved_stats.log_metric_to_accumulate('problems', 0)
                log_scalar('solution', step+log_num, 0)
                log_scalar('solution/length', step + log_num, -1)
                log_text('trajectory_actions', f'{step + log_num}: unsolved', False)
                log_scalar('solution/n_subgoals', step + log_num, -1)

            log_scalar('verificator failed', step + log_num, result['additional_info']['verificator_failed'])

            log_scalar_metrics('predictions', step+log_num, result['additional_info']['predictions'])
            # log_scalar('problems', step + n_logs, step + n_logs)

            # if result['tree_metrics']['nodes'] < 100:
            for i, verification in enumerate(result['additional_info']['verifications']):
                if i in self.verifications.keys():
                    self.verifications[i] = self.verifications[i] + verification
                else:
                    self.verifications[i] = verification
            # else:
            #     print('Too long episode:', result['tree_metrics']['nodes'], 'nodes')

            joint_calls = 0
            for key in result['additional_info']:
                if 'calls/' in key:
                    self.calls_stats.log_metric_to_accumulate(key + '_sum', result['additional_info'][key])
                    log_scalar(key, step + log_num, result['additional_info'][key])
                    joint_calls += result['additional_info'][key]
            self.calls_stats.log_metric_to_accumulate('calls/joint_sum', joint_calls)
            log_scalar('calls/joint', step + log_num, joint_calls)

            if self.budget_checkpoints is not None:
                for budget in self.budget_checkpoints:
                    if result['tree_metrics']['expanded_nodes'] <= budget and solved:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_exp_nodes', 1)
                    else:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_exp_nodes', 0)

                    if result['tree_metrics']['nodes'] <= budget and solved:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_nodes', 1)
                    else:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_nodes', 0)

            if self.real_budget_checkpoints is not None:
                for budget in self.real_budget_checkpoints:
                    if result['tree_metrics']['real_cost_final'] <= budget and solved:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_evaluations', 1)
                    else:
                        self.solved_stats.log_metric_to_average(f'rate/{budget}_evaluations', 0)

        for i, verification in self.verifications.items():
            log_text(f'verifications of builder {i}', str(verification), False)
            log_text(f'(normalized) verifications of builder {i}',
                     str([verification[0] / sum(verification[0]), verification[1] / sum(verification[1])]), False)

        log_scalar_metrics('solved', step+n_logs, self.solved_stats.return_scalars())
        log_scalar_metrics('calls', step+n_logs, self.calls_stats.return_scalars())
        log_scalar_metrics('solution/distances', step+n_logs, self.distance_stats.return_scalars())

    def log_solution(self, solution, trajectory_actions, input_problem, step):
        if solution is not None:
            solution_str = f'Problem {step} : {solution[0].hash} \n'

            for subgoal_num, node in enumerate(solution[1:]):
                solution_str += f'subgoal {subgoal_num} : {node.hash} \n'
            solution_str += '\n \n'
            solution_str += 'Actions: \n'

            for action_num, action in enumerate(trajectory_actions):
                solution_str += f'action {action_num}: ({action[0]}, {[entity_to_seq_string(ent) for ent in action[1:]]} ) \n'
        else:
            solution_str = f'Unsolved problem {step} : {logic_statement_to_seq_string(input_problem["observation"]["objectives"][0])} \n \n'

        log_text('solution', solution_str, True)

