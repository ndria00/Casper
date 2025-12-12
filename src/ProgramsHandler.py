from clingo.ast import parse_string
from .FlipConstraintRewriter import FlipConstraintRewriter
from .QuantifiedProgram import QuantifiedProgram, ProgramQuantifier
from enum import Enum

class ASPQType(str, Enum):
    EXISTS_FIRST = "exists_first"
    FORALL_FIRST = "forall_first"

class ProgramsHandler:
    FLIP_CONSTRAINT_PREDICATE_NAME = "unsat_c"
    encoding : str
    instance : str
    original_programs_list : list
    flipped_constraint : QuantifiedProgram
    program_type : ASPQType

    def flip_constraint(self):
        flipConstraintRewriter = FlipConstraintRewriter(f"{self.FLIP_CONSTRAINT_PREDICATE_NAME}{len(self.original_programs_list)}")
        constraint_program = self.original_programs_list[len(self.original_programs_list)-1]
        parse_string(constraint_program.rules, lambda stm: (flipConstraintRewriter(stm)))
        self.flipped_constraint = QuantifiedProgram(rules="\n".join(flipConstraintRewriter.program), weak_constraints=[], program_type=ProgramQuantifier.CONSTRAINTS, program_name=constraint_program.name, head_predicates=flipConstraintRewriter.head_predicates) 

    def p(self, idx):
        if idx < 0 or idx >= len(self.original_programs_list):
            raise Exception("Incorrect program index")
        return self.original_programs_list[idx]
    
    def last_exists(self):
        #constrant in \Pi -> last program is at index -2
        if self.original_programs_list[len(self.original_programs_list)-1].program_type == ProgramQuantifier.CONSTRAINTS:
            return self.original_programs_list[len(self.original_programs_list)-2].program_type == ProgramQuantifier.EXISTS
        #no constrant in \Pi -> last program is at index -1
        return self.original_programs_list[len(self.original_programs_list)-1].program_type == ProgramQuantifier.EXISTS
    
    
    def c(self):
        return self.original_programs_list[len(self.original_programs_list)-1]

    def neg_c(self):
        return self.flipped_constraint

    def __init__(self, original_programs_list, instance):
        self.original_programs_list = original_programs_list
        self.instance = instance
        self.flipped_constraint = None
        self.compute_program_type()
        #add empty constraint program if no constraint program was parsed
        self.flip_constraint()


    def check_aspq_type(self):
        if len(self.original_programs_list) > 3:
            for program in self.original_programs_list:
                if program.contains_weak():
                    print("This solver can only work with aspq programs with weak  with uo to two quantifiers")
                    exit(1)

        for i in range(0, len(self.original_programs_list)):
            program = self.original_programs_list[i]
            if program.program_type == ProgramQuantifier.CONSTRAINTS and i != len(self.original_programs_list)-1:
                raise Exception("Constraint is not the last program")
            if i < len(self.original_programs_list)-1:
                if self.original_programs_list[i].program_type == self.original_programs_list[i-1].program_type and not self.original_programs_list[i].contains_weak() and not self.original_programs_list[i-1].contains_weak():
                    raise Exception("Quantifiers are not alternating")

        #set program type
        if self.original_programs_list[0].program_type == ProgramQuantifier.FORALL:
            self.program_type = ASPQType.FORALL_FIRST
        elif self.original_programs_list[0].program_type == ProgramQuantifier.EXISTS:
            self.program_type = ASPQType.EXISTS_FIRST
        else:
            raise Exception("First program is neither forall nor exists")


    def print_programs(self):
        for prg in self.original_programs_list:
            if prg.program_type == ProgramQuantifier.EXISTS:
                print("EXISTS PROGRAM")
            elif prg.program_type == ProgramQuantifier.FORALL:
                print("FORALL PROGRAM")
            else:
                print("CONSTRAINTS PROGRAM")
            print(f"{prg.rules}")
    
    def exists_first(self) -> bool:
        return self.program_type == ASPQType.EXISTS_FIRST
    
    def forall_first(self) -> bool:
        return self.program_type == ASPQType.FORALL_FIRST
    
    def compute_program_type(self):
        if self.original_programs_list[0].program_type == ProgramQuantifier.FORALL:
            self.program_type = ASPQType.FORALL_FIRST
        elif self.original_programs_list[0].program_type == ProgramQuantifier.EXISTS:
            self.program_type = ASPQType.EXISTS_FIRST
        else:
            raise Exception("First program is neither forall nor exists")