from clingo.ast import parse_string
from .FlipConstraintRewriter import FlipConstraintRewriter
from .MyProgram import MyProgram, ProgramQuantifier
from .RelaxedRewriter import RelaxedRewriter
from .SplitProgramRewriter import SplitProgramRewriter
from enum import Enum

class ASPQType(str, Enum):
    EXISTS_FIRST = "exists_first"
    FORALL_FIRST = "forall_first"

class ProgramsHandler:
    
    encoding : str
    instance : str
    original_programs_list : list
    flipped_constraint : MyProgram
    program_type : ASPQType

    def flip_constraint(self):
        flipConstraintRewriter = FlipConstraintRewriter("unsat_c")
        constraint_program = self.original_programs_list[len(self.original_programs_list)-1]
        parse_string("\n".join(constraint_program.rules), lambda stm: (flipConstraintRewriter(stm)))
        self.flipped_constraint = MyProgram(rules=flipConstraintRewriter.program, program_type=ProgramQuantifier.CONSTRAINTS, program_name=constraint_program.name, head_predicates=flipConstraintRewriter.head_predicates) 

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
        #add empty constraint program if no constraint program was parsed
        if self.original_programs_list[len(self.original_programs_list)-1].program_type != ProgramQuantifier.CONSTRAINTS:
            self.original_programs_list.append(MyProgram([], ProgramQuantifier.CONSTRAINTS, "c", set()))
        self.flip_constraint()


    def check_aspq_type(self):
        for i in range(0, len(self.original_programs_list)):
            program = self.original_programs_list[i]
            if program.program_type == ProgramQuantifier.CONSTRAINTS and i != len(self.original_programs_list)-1:
                raise Exception("Constraint is not the last program")
            if i < len(self.original_programs_list)-1 and self.original_programs_list[i].program_type == self.original_programs_list[i-1].program_type:
                raise Exception("Quantifiers are not alternating")

        #TODO adapt this for collapsing non-alternating quantifiers
        #some program was not specified
        # if len(self.programs) != 3:
        #     if len(self.programs) == 1:
        #         if self.programs[0].program_type == ProgramQuantifier.FORALL:
        #             raise Exception("Only forall specified - this setting is not allowed")
        #         #if self.programs[0].program_type == ProgramQuantifier.EXISTS or self.programs[0].program_type == ProgramQuantifier.CONSTRAINTS:
        #         self.program_type = ASPQType.EXISTS
        #         #make C an exists... it is the same as having a single program with exists
        #         self.programs[0].program_type = ProgramQuantifier.EXISTS
        #         self.exists_program = self.programs[0]
        #         self.constraint_program = None
        #     else: # 2 programs
        #         if self.programs[0].program_type == ProgramQuantifier.EXISTS:
        #             #if P2 is constraint, then I can consider a single exists program as P2 \cup P1  
        #             if not self.constraint_program is None:
        #                 self.program_type = ASPQType.EXISTS
        #                 self.programs[0].head_predicates = self.programs[0].head_predicates | self.constraint_program.head_predicates
        #                 self.programs[0].rules = self.programs[0].rules + self.constraint_program.rules
        #                 self.programs.pop()
        #                 self.constraint_program = None
        #         else:
        #             self.program_type = ASPQType.FORALL
        # else:
        #set program type
        if self.original_programs_list[0].program_type == ProgramQuantifier.FORALL:
            self.program_type = ASPQType.FORALL_FIRST
            print("Solving a forall-exists program")
        elif self.original_programs_list[0].program_type == ProgramQuantifier.EXISTS:
            self.program_type = ASPQType.EXISTS_FIRST
            print("Solving an exists-forall program")
        else:
            raise Exception("First program is neither forall nor exists")


    def print_programs(self):
        for prg in self.original_programs_list:
            if prg.program_quantifier == ProgramQuantifier.EXISTS:
                print("EXISTS PROGRAM")
            elif prg.program_quantifier == ProgramQuantifier.FORALL:
                print("FORALL PROGRAM")
            else:
                print("CONSTRAINTS PROGRAM")
            print(f"{prg.rules}")
    
    def exists_first(self) -> bool:
        return self.program_type == ASPQType.EXISTS_FIRST
    
    def forall_first(self) -> bool:
        return self.program_type == ASPQType.FORALL_FIRST