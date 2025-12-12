from abc import ABC, abstractmethod

#Takes P_2, ..., P_n : C as programs
class RefinementRewriter(ABC):
    SUFFIX_P : str = "_p_"
    SUFFIX_N : str = "_n_"
    FAIL_ATOM_NAME = "fail_"

    original_programs_list : list
    rewritten_programs_list : list

    @abstractmethod
    def __init__(self, original_programs, program_c, program_neg_c, ground_transformation):
        pass

    def rewrite(self, counterexample, iteration):
        pass
        
    @abstractmethod
    def refined_program(self):
        pass
    
    @abstractmethod
    def compute_placeholder_program(self):
        pass