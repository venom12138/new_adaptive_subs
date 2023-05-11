from proof_system.logic_functions import necessary_logic_functions
from proof_system.graph_seq_conversion import Parser
from copy import deepcopy
import networkx as nx
import matplotlib.pyplot as plt
from visualization.seq_parse import my_logic_statement_to_seq_string
import misc.global_var as global_var
import os

# 这个类应当起到为prover提供conditions，objectives的作用，也就是说，先建立graph，最后选择用到的部分
# 再放入prover中，
# ProofNode：应当只有logic_statement和lemma，没有所谓的assumptions，conclusions，basic_conditions，parents node里的ls就是assumptions，没有parent的node就是basic_conditions
class ProofNode:
    def __init__(self, step_dict, lemma_type):
        """
        This ProofNode is responsible for document the proof state, every logic statement is a node.
        Every logic statement is coming from several logic_statement and a lemma 
        :param step: lemma's operands,lemma name, and so on
            :param _logic_statement: the ls of the node
            :param lemma: the lemma used to get the node
        :param lemma_type: axiom or theorem
        :param parents: the new node's parents
        """
        self.lemma = step_dict["lemma"] # None
        self._logic_statement = step_dict["logic_statement"]
        self._operands = step_dict["operands"] # []
        self.lemma_type = lemma_type # None, axiom, ordered_axiom, theorem
        if lemma_type == "axiom" or lemma_type == "ordered_axiom":
            assert 'step' in step_dict.keys()
            self.step = step_dict['step']
            assert self.step["lemma"].name == self.lemma.name
            for i, operand in enumerate(self.step["input_entities"]):
                assert operand.name == self._operands[i].name
        
        self.index = None
        self.parents_idxs = []
        self.children_idxs = []
        self.name = self._logic_statement.name
        self.longest_depth = 0
        self.ancesters_num = 0
        
    def is_basic_condtion(self):
        return len(self.parents_idxs) == 0
    
    def get_ls_length(self):
        return len(my_logic_statement_to_seq_string(self._logic_statement))

class ProofGraph:
    def __init__(self,):
        """
        ProofGraph is the graph of the proof, which is a DAG
        """
        self.nodes = [] # list of ProofNode
        self.nd_id2node = {}
        self.nd_name2id = {}
        
    def add_node(self, node, parents=None):
        assert isinstance(node, ProofNode)
        if node.name in self.nd_name2id.keys():
            return
        idx = len(self.nodes)
        node.index = idx
        self.nd_name2id[node.name] = idx
        self.nd_id2node[idx] = node
        
        if parents != None:
            for parent in parents:
                assert parent.name in self.nd_name2id.keys()
                p_idx = self.nd_name2id[parent.name]
                p_node = self.nd_id2node[p_idx]
                node.longest_depth = max(node.longest_depth, p_node.longest_depth + 1)
                node.ancesters_num += p_node.ancesters_num + 1
                if idx not in p_node.children_idxs:
                    p_node.children_idxs.append(idx)
                if p_idx not in node.parents_idxs:
                    node.parents_idxs.append(p_idx)
        
        self.nodes.append(node)
        return node.index
    
    def is_node_in_graph(self, node):
        return node.name in self.nd_name2id.keys()
    
    def get_leaf_nodes(self):
        leaf_nodes = []
        for node in self.nodes:
            if len(node.children_idxs) == 0:
                leaf_nodes.append(node)
        return leaf_nodes
    
    def get_root_nodes(self):
        root_nodes = []
        for node in self.nodes:
            if len(node.parents_idxs) == 0:
                root_nodes.append(node)
        return root_nodes
    
    # given node in a proof graph, return the compact proof graph related to the node
    def compact_proof_graph(self, node):
        assert node.name in self.nd_name2id.keys()
        node = deepcopy(self.nd_id2node[self.nd_name2id[node.name]])
        proof_path = []
        open_nodes = [node]
        compact_children_dict = {node.name: []}
        compact_parents_dict = {}
        # get all the nodes in the proof path
        while len(open_nodes) > 0:
            nd = open_nodes.pop(0)
            if nd.name not in compact_parents_dict.keys():
                compact_parents_dict[nd.name] = []
            proof_path.append(nd)
            for parent_idx in nd.parents_idxs:
                parent = deepcopy(self.nd_id2node[parent_idx])
                compact_parents_dict[nd.name].append(parent.name)
                if parent.name not in compact_children_dict.keys():
                    compact_children_dict[parent.name] = [nd.name]
                    open_nodes.append(parent)
                else:
                    compact_children_dict[parent.name].append(nd.name)
        
        # reverse proof_path
        proof_path.reverse()
        compact_graph = ProofGraph()
        compact_graph.nodes = list(set(proof_path))
        # construct graph
        for idx, node in enumerate(compact_graph.nodes):
            compact_graph.nd_id2node[idx] = node
            compact_graph.nd_name2id[node.name] = idx
            node.index = idx
        # construct parents and children
        for node in compact_graph.nodes:
            node_parents_names = list(set(compact_parents_dict[node.name]))
            node_children_names = list(set(compact_children_dict[node.name]))
            node.parents_idxs = [compact_graph.nd_name2id[name] for name in node_parents_names]
            node.children_idxs = [compact_graph.nd_name2id[name] for name in node_children_names]
        assert len(compact_graph.get_leaf_nodes()) == 1
        return compact_graph
    
    def visualize(self,):
        self.G = nx.DiGraph()
        for node in self.nodes:
            if node.lemma is not None:
                node_name = my_logic_statement_to_seq_string(node) + '\n' + node.lemma.name
            else:
                node_name = my_logic_statement_to_seq_string(node)
            if node.parents_idxs == []:
                self.G.add_node(node_name, color='red')
            elif node.children_idxs == []:
                self.G.add_node(node_name, color='green')
            else:
                self.G.add_node(node_name, color='blue')
        for node in self.nodes:
            for parent_idx in node.parents_idxs:
                parent = self.nd_id2node[parent_idx]
                if parent.lemma is not None:
                    fst_name = my_logic_statement_to_seq_string(parent) + '\n' + parent.lemma.name
                else:
                    fst_name = my_logic_statement_to_seq_string(parent)
                
                if node.lemma is not None:
                    snd_name = my_logic_statement_to_seq_string(node) + '\n' + node.lemma.name
                else:
                    snd_name = my_logic_statement_to_seq_string(node)
                
                self.G.add_edge(fst_name, snd_name, )
        colors = [node_dict['color'] for node_dict in self.G._node.values()]
        nx.draw(self.G, arrowstyle='->', arrowsize=50, node_color=colors, with_labels=True, font_size=5)
        global_var.set_value('COUNT', global_var.get_value('COUNT') + 1)
        plt.rcParams['savefig.dpi'] = 500 #图片像素
        plt.rcParams['figure.dpi'] = 300 #分辨率
        if os.path.exists("./visuals") == False:
            os.mkdir("./visuals")
        plt.savefig(f"./visuals/{global_var.get_value('COUNT')}.jpg")
        print(f"save to ./visuals/{global_var.get_value('COUNT')}.jpg")
        # plt.show()
        # plt.waitforbuttonpress()
        plt.cla()
        
        # plt.show()