import pickle

path = '/home/venom/projects/Automated_Theorem_Proving/new_INT/problems/ordered_field/k=5_l=15/train/steps_1.p'
with open(path, 'rb') as f:  
    data_dict = pickle.loads(f.read())
print(data_dict)