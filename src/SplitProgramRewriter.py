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
import re
import clingo

from .WeakConstraint import WeakConstraint
from .QuantifiedProgram import QuantifiedProgram, ProgramQuantifier
from .Rewriter import Rewriter
from enum import Enum
from clingo.ast import parse_string
import sys


class SplitProgramRewriter(Rewriter):
    programs: list[QuantifiedProgram]
    global_weak : QuantifiedProgram
    rules : list[str]
    cur_program_quantifier : ProgramQuantifier
    curr_program_name : str
    curr_weak_constraints : list
    program_is_open : bool
    encoding_program : str

    def __init__(self, encoding_program) -> None:
        super().__init__()
        self.programs = []
        self.cur_program_rules = []
        self.curr_weak_constraints = []
        self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
        self.curr_program_name = "c"
        self.program_is_open = False
        self.constraint_program = None
        self.encoding_program = encoding_program
        self.optimization_program = False
        self.global_weak = None
        parse_string(encoding_program, lambda stm: (self(stm)))
        self.closed_program()

        if not self.global_weak is None and len(self.programs) == 0:
            raise Exception("Only weak program specified - this is not allowed")
        if not self.global_weak is None and self.programs[0].program_type == ProgramQuantifier.FORALL:
            print("WARNING: global weak are ignored when first program is a forall program")
            self.global_weak = None
        if self.programs[len(self.programs)-1].program_type != ProgramQuantifier.CONSTRAINTS:
            self.programs.append(QuantifiedProgram("", [], ProgramQuantifier.CONSTRAINTS, "c", set()))

    def visit_Comment(self, value):
        value_str = str(value)
        is_exist_directive = not re.match("%@exists", value_str) is None
        is_forall_directive = not re.match("%@forall", value_str) is None
        is_constraint_directive = not re.match("%@constraint", value_str) is None
        is_global_weak_directive = not re.match("%@global", value_str) is None

        if is_exist_directive or is_forall_directive or is_constraint_directive or is_global_weak_directive:
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
        elif is_global_weak_directive:
            self.program_is_open = True
            self.cur_program_quantifier = ProgramQuantifier.GLOBAL_WEAK
            self.curr_program_name = "global_weak"
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
            program = QuantifiedProgram("\n".join(self.cur_program_rules), self.curr_weak_constraints, self.cur_program_quantifier, self.curr_program_name, self.head_predicates)
            if self.cur_program_quantifier != ProgramQuantifier.GLOBAL_WEAK:
                self.programs.append(program)
            else:
                self.global_weak = program
            self.program_is_open = False
        self.cur_program_rules = []
        self.curr_weak_constraints = []
        self.head_predicates = set()

    def print_program_types(self):
        print("Prorgam is of the form: [", end="")
        
        for i in range(len(self.programs)):
            prg = self.programs[i]
            if prg.program_type == ProgramQuantifier.EXISTS:
                if prg.contains_weak():
                    print("\\exists_weak", end="")
                else:
                    print("\\exists", end="")
            elif prg.program_type == ProgramQuantifier.FORALL:
                if prg.contains_weak():
                    print("\\forall_weak", end="")
                else:
                    print("\\forall", end="")
            elif prg.program_type == ProgramQuantifier.CONSTRAINTS:
                print("\\constraint", end="")
            else:
                print("None", end="")
            if i != len(self.programs)-1:
                print(", ", end="")
        if not self.global_weak is None:
            print(", \\global_weak", end="")
        print("]")
    
    def aspq_program_contains_local_weak(self):
        for program in self.programs:
            if program.contains_weak():
                return True
        return False    
    
    #\exits \exitst_w, \forall \forall_w or in opposite order
    def non_alternating_aspq_with_weaks(self):
        if not self.aspq_program_contains_local_weak():
            return False
        first_program_type = self.programs[0].program_type
        for program in self.programs:
            if not program.constraint() and program.program_type != first_program_type:
                return False
        return True

    def visit_Minimize(self, node):
        self.optimization_program = True
        terms = []
        for term in node.terms:
            terms.append(str(term))
        weight = str(node.weight)
        if not node.priority is None:
            level = str(node.priority)
        else:
            level = "0"
        body = ",".join([str(lit) for lit in node.body])
        weak = WeakConstraint(body, weight, level, terms)
        self.curr_weak_constraints.append(weak)
        return node.update(**self.visit_children(node))