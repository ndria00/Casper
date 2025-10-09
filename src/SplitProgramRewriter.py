import re
import clingo
from .MyProgram import MyProgram, ProgramQuantifier
from .Rewriter import Rewriter
from enum import Enum
from clingo.ast import parse_string
import sys


class SplitProgramRewriter(Rewriter):
    programs: list[MyProgram]
    rules : list[str]
    cur_program_quantifier : ProgramQuantifier
    curr_program_name : str
    program_is_open : bool
    encoding_program : str

    def __init__(self, encoding_program) -> None:
        super().__init__()
        self.programs = []
        self.cur_program_rules = []
        self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
        self.curr_program_name = "c"
        self.program_is_open = False
        self.constraint_program = None
        self.encoding_program = encoding_program
        parse_string(encoding_program, lambda stm: (self(stm)))
        self.closed_program()
        self.print_program_types()

    def visit_Comment(self, value):
        value_str = str(value)
        is_exist_directive = not re.match("%@exists", value_str) is None
        is_forall_directive = not re.match("%@forall", value_str) is None
        is_constraint_directive = not re.match("%@constraint", value_str) is None
        #when an exists directive is found after another exists directive the programs are merged toghether
        #same reasoning for forall
        if (is_exist_directive and self.cur_program_quantifier != ProgramQuantifier.EXISTS) or (is_forall_directive and self.cur_program_quantifier != ProgramQuantifier.FORALL) or is_constraint_directive: 
            self.closed_program()
    
        if is_exist_directive:
            if not self.constraint_program is None:
                raise Exception("Constraint program must appear as last program")
            self.program_is_open = True
            self.cur_program_quantifier = ProgramQuantifier.EXISTS
            self.curr_program_name = f"{len(self.programs)+1}"
        elif is_forall_directive:
            if not self.constraint_program is None:
                raise Exception("Constraint program must appear as last program")
            self.program_is_open = True
            self.cur_program_quantifier = ProgramQuantifier.FORALL
            self.curr_program_name = f"{len(self.programs)+1}"
        elif is_constraint_directive:
            self.program_is_open = True
            self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
            self.curr_program_name = "c"
        # else:
            #print("Spurious comment subprogram start")
        
        

    def visit_Rule(self, node):
        self.cur_program_rules.append(str(node))
        head  = node.head
        if head.ast_type == clingo.ast.ASTType.Literal:
            if not head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
                self.extract_predicate_from_literal(head)         
        elif clingo.ast.ASTType.Aggregate:
            self.extract_predicate_from_choice(head)
        return node.update(**self.visit_children(node))
    
    def closed_program(self):
        program_str = "".join(self.cur_program_rules)
        if self.program_is_open:
            if not re.search(r'fail_\d+|unsat_c', program_str) is None:
                print("Predicate names and constants of the form fail_\\d+ or unsat_c are not allowed... Exiting")
                sys.exit(1)
            program = MyProgram("\n".join(self.cur_program_rules), self.cur_program_quantifier, self.curr_program_name, self.head_predicates)
            self.programs.append(program)
            self.program_is_open = False
        self.cur_program_rules = []
        self.head_predicates = set()

    def print_program_types(self):
        print("Prorgam is of the form: [", end="")
        
        for i in range(len(self.programs)):
            prg = self.programs[i]
            if prg.program_type == ProgramQuantifier.EXISTS:
                print("\\exists", end="")
            elif prg.program_type == ProgramQuantifier.FORALL:
                print("\\forall", end="")
            elif prg.program_type == ProgramQuantifier.CONSTRAINTS:
                print("\\constraint", end="")
            else:
                print("None", end="")
            if i != len(self.programs)-1:
                print(", ", end="")

        print("]")