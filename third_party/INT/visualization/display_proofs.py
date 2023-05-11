import argparse
import pickle

from visualization.latex_parse import step_to_latex


def display_a_proof(steps):
    proof_string = ""
    for j, step in enumerate(steps):
        proof_string += "-" * 50 + f"Step {j+1}" + "-" * 50 + "\n"
        proof_string += step_to_latex(step) + "\n"
    return proof_string

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Display proofs')
    parser.add_argument('--proof-file', type=str, required=True, help='Proofs to display come from this file')
    parser.add_argument('--how-many', type=int, required=True, help='How many proofs to display')
    args = parser.parse_args()

    with open(args.proof_file, 'rb') as proofs_h:
        proof_dict = pickle.load(proofs_h)
        proof = list(proof_dict.values())[0][0]
        for _, proofs in proof_dict.items():
            for i, proof in enumerate(proofs):
                if i >= args.how_many:
                    break
                # print(f"proof:{proof}")
                print("*" * 50 + f"Proof {i+1}" + "*" * 50)
                print(display_a_proof(proof))
