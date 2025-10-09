import copy
from enum import Enum

class ProgramQuantifier(str, Enum):
    EXISTS = "exists"
    FORALL = "forall"
    CONSTRAINTS = "constraint"
class MyProgram:
    rules : str
    program_type : ProgramQuantifier
    name : str
    head_predicates : set

    def __init__(self, rules, program_type, program_name, head_predicates) -> None:
        self.rules = rules
        self.program_type = program_type
        self.name = program_name
        self.head_predicates = copy.copy(head_predicates)
    
    def exists(self):
        return self.program_type == ProgramQuantifier.EXISTS
    
    def forall(self):
        return self.program_type == ProgramQuantifier.FORALL
    
    def constraint(self):
        return self.program_type == ProgramQuantifier.CONSTRAINTS

    def print_head_predicates(self):
        for predicate in self.head_predicates : 
            print(f"Head predicate {predicate}, ")

    def __str__(self):
        quantifier = ""
        if self.program_type == ProgramQuantifier.EXISTS:
            quantifier = "\\exists"
        elif self.program_type == ProgramQuantifier.FORALL:
            quantifier = "\\forall"
        elif self.program_type == ProgramQuantifier.CONSTRAINTS:
            quantifier = "\\constraint"
        else:
            raise Exception("Unexpected quantifier")
        return f"[{quantifier}] -> {self.rules}"