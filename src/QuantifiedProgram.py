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
from enum import Enum

class ProgramQuantifier(str, Enum):
    EXISTS = "exists"
    FORALL = "forall"
    CONSTRAINTS = "constraint"
    GLOBAL_WEAK = "global"

class QuantifiedProgram:
    MIN_WEAK_LEVEL : int = 0
    rules : str
    weak_constraints : list
    program_type : ProgramQuantifier
    name : str
    head_predicates : set
    output_predicates : set

    def __init__(self, rules, weak_constraints, program_type, program_name, head_predicates) -> None:
        self.rules = rules
        self.weak_constraints = weak_constraints
        self.weak = len(self.weak_constraints) > 0
        self.program_type = program_type
        self.name = program_name
        self.head_predicates = set(head_predicates)
        self.output_predicates = set()
    
    def exists(self):
        return self.program_type == ProgramQuantifier.EXISTS
    
    def forall(self):
        return self.program_type == ProgramQuantifier.FORALL
    
    def quantifier(self):
        return self.program_type
    
    def constraint(self):
        return self.program_type == ProgramQuantifier.CONSTRAINTS

    def global_weak(self):
        return self.program_type == ProgramQuantifier.GLOBAL_WEAK

    def print_head_predicates(self):
        for predicate in self.head_predicates : 
            print(f"Head predicate {predicate}, ")
    
    def set_output_predicates(self, predicates):
        self.output_predicates = set(predicates)

    def contains_weak(self):
        return len(self.weak_constraints) > 0

    def __str__(self):
        quantifier = ""
        if self.program_type == ProgramQuantifier.EXISTS:
            quantifier = "%@exists"
        elif self.program_type == ProgramQuantifier.FORALL:
            quantifier = "%@forall"
        elif self.program_type == ProgramQuantifier.CONSTRAINTS:
            quantifier = "%@constraint"
        elif self.program_type == ProgramQuantifier.GLOBAL_WEAK:
            quantifier = "%@global"
        else:
            raise Exception("Unexpected quantifier")
        weak_repr = "\n".join(str(weak) for weak in self.weak_constraints)
        return f"{quantifier}\n{self.rules}\n{weak_repr}"