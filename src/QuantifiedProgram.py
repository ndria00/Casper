from enum import Enum

class ProgramQuantifier(str, Enum):
    EXISTS = "exists"
    FORALL = "forall"
    CONSTRAINTS = "constraint"
class QuantifiedProgram:
    MIN_WEAK_LEVEL : str = 0
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
        else:
            raise Exception("Unexpected quantifier")
        return f"{quantifier}\n{self.rules}"