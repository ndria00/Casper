# Copyright [2025] [Andrea Cuteri, Giuseppe Mazzotta and Francesco Ricca]

#    Licensed under the Apache License, Version 2.0 (the "License");
#    you may not use this file except in compliance with the License.
#    You may obtain a copy of the License at

#        http://www.apache.org/licenses/LICENSE-2.0

#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#    See the License for the specific language governing permissions and
#    limitations under the License.
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