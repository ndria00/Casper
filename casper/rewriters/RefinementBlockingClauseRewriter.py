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
from casper.language import QuantifiedProgram, ProgramQuantifier
from .ReductRewriter import ReductRewriter
from .OrProgramRewriter import OrProgramRewriter
from .RefinementRewriter import RefinementRewriter


#Takes P_2, ..., P_n : C as programs
#flips quantifiers and constraint if the first program is \forall (i.e. the outermost program was a \exists)
#the first two programs collapse into a single ASP program
class RefinementBlockingClauseRewriter(RefinementRewriter):

    symbols_defined_in_abstraction : dict
    rewritten_program : str
    curr_candiate : list 

    def __init__(self, symbols_defined_in_abstraction):
        self.symbols_defined_in_abstraction = symbols_defined_in_abstraction

    def rewrite(self, candidate, iteration):
        self.curr_candiate = candidate
        self.rewritten_program = ":-"
        for symbol in self.symbols_defined_in_abstraction.keys():
            if symbol in candidate:
                self.rewritten_program += f"{symbol},"
            else:
                self.rewritten_program += f"not {symbol},"

        self.rewritten_program = self.rewritten_program[:-1]
        self.rewritten_program += "."
        
    def refined_program(self):
        return self.rewritten_program        


    def compute_placeholder_program(self):
        pass