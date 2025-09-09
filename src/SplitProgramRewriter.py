import re
import clingo
from .MyProgram import MyProgram, ProgramQuantifier
from .Rewriter import Rewriter
from enum import Enum

class ASPQType(str, Enum):
    EXISTS_FORALL = "exists_forall"
    FORALL_EXISTS = "forall_exists"
    EXISTS = "exists"
    FORALL = "forall"

class SplitProgramRewriter(Rewriter):
    programs: list[MyProgram]
    forall_program : MyProgram
    exists_program : MyProgram
    constraint_program : MyProgram
    rules : list[str]
    cur_program_quantifier : ProgramQuantifier
    program_type : ASPQType
    program_name : str
    open_program : bool

    def __init__(self) -> None:
        super().__init__()
        self.programs = []
        self.cur_program_rules = []
        self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
        self.program_name = "c"
        self.open_program = False
        self.forall_program = None
        self.exists_program = None
        self.constraint_program = None

    def visit_Comment(self, value):
        value_str = str(value)
        is_exist_directive = not re.match("%@exists", value_str) is None
        is_forall_directive = not re.match("%@forall", value_str) is None
        is_constraint_directive = not re.match("%@constraint", value_str) is None
        if is_exist_directive or is_forall_directive or is_constraint_directive:
            self.closed_program()
    
        if is_exist_directive:
            if not self.constraint_program is None:
                raise Exception("Constraint program must appear as last program")
            self.open_program = True
            self.cur_program_quantifier = ProgramQuantifier.EXISTS
            self.program_name = f"p_{len(self.programs)+1}"
            # print("Existential subprogram start")
        elif is_forall_directive:
            if not self.constraint_program is None:
                raise Exception("Constraint program must appear as last program")
            self.open_program = True
            self.cur_program_quantifier = ProgramQuantifier.FORALL
            self.program_name = f"p_{len(self.programs)+1}"
            # print("Universal subprogram start")
        elif is_constraint_directive:
            self.open_program = True
            self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
            self.program_name = "c"
            # print("Constraints subprogram start")
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
        # print(f"Found rule {value}\n")
    
    def closed_program(self):
        if self.open_program:
            if len(self.programs) >= 3:
                raise Exception("This solver can only work with two-level ASPQ")
            program = MyProgram(self.cur_program_rules, self.cur_program_quantifier, self.program_name,self.head_predicates)
            self.programs.append(program)
            if self.cur_program_quantifier == ProgramQuantifier.FORALL:
                self.forall_program = program
            elif self.cur_program_quantifier == ProgramQuantifier.EXISTS:
                self.exists_program = program
            elif self.cur_program_quantifier == ProgramQuantifier.CONSTRAINTS:
                self.constraint_program = program
            else:
                raise Exception("Unknown program type")
            self.open_program = False
        self.cur_program_rules = []
        self.head_predicates = set()
    
    def check_aspq_type(self):
        self.closed_program()

        #some program was not specified
        if len(self.programs) != 3:
            if len(self.programs) == 1:
                if self.programs[0].program_type == ASPQType.FORALL:
                    raise Exception("Only forall specified - this setting is not allowed")
                #if self.programs[0].program_type == ProgramQuantifier.EXISTS or self.programs[0].program_type == ProgramQuantifier.CONSTRAINTS:
                self.program_type = ASPQType.EXISTS
                #make C an exists... it is the same as having a single program with exists
                self.programs[0].program_type = ProgramQuantifier.EXISTS
                self.exists_program = self.programs[0]
                self.constraint_program = None
            else: # 2 programs
                if self.programs[0].program_type == ProgramQuantifier.EXISTS:
                    #if P2 is constraint, then I can consider a single exists program as P2 \cup P1  
                    if not self.constraint_program is None:
                        self.program_type = ASPQType.EXISTS
                        self.programs[0].head_predicates = self.programs[0].head_predicates | self.constraint_program.head_predicates
                        self.programs[0].rules = self.programs[0].rules + self.constraint_program.rules
                        self.programs.pop()
                        self.constraint_program = None
                else:
                    self.program_type = ASPQType.FORALL
        else:
            #set program type
            if self.programs[0] == self.forall_program:
                self.program_type = ASPQType.FORALL_EXISTS
                print("Solving a forall-exists program")
            elif self.programs[0] == self.exists_program:
                self.program_type = ASPQType.EXISTS_FORALL
                print("Solving an exists-forall program")
            else:
                raise Exception("First program is neither forall nor exists")
    
    def print_programs(self):
        for prg in self.programs:
            if prg.program_quantifier == ProgramQuantifier.EXISTS:
                print("EXISTS PROGRAM")
            elif prg.program_quantifier == ProgramQuantifier.FORALL:
                print("FORALL PROGRAM")
            else:
                print("CONSTRAINTS PROGRAM")
            print(f"{prg.rules}")

    def exists(self) -> bool:
        return self.program_type == ASPQType.EXISTS
    
    def exists_forall(self) -> bool:
        return self.program_type == ASPQType.EXISTS_FORALL
    
    def forall_exists(self) -> bool:
        return self.program_type == ASPQType.FORALL_EXISTS