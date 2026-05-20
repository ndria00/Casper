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
from clingo.ast import parse_string
import clingo.ast as ast
from casper.language import WeakConstraint
from casper.language import QuantifiedProgram, ProgramQuantifier
from casper.utils import SolverSettings
from .Rewriter import Rewriter


class SplitProgramRewriter(Rewriter):
    programs: list[QuantifiedProgram]
    global_weak : QuantifiedProgram
    cur_program_rules : list[str]
    curr_program_constraints : list[str]
    curr_program_constraints_clone : list[str]
    cur_program_quantifier : ProgramQuantifier
    curr_program_name : str
    curr_weak_constraints : list
    curr_program_contains_choice : bool
    curr_program_contains_disjunction : bool
    curr_program_contains_aggregates : bool
    program_is_open : bool
    encoding_program : str
    handle_disjunction : bool

    def __init__(self, encoding_program, handle_disjunction) -> None:
        super().__init__()
        self.programs = []
        self.cur_program_rules = []
        self.curr_program_constraints = []
        self.curr_program_constraints_clone = []
        self.curr_weak_constraints = []
        self.cur_program_quantifier = ProgramQuantifier.CONSTRAINTS
        self.curr_program_name = "c"
        self.program_is_open = False
        self.constraint_program = None
        self.encoding_program = encoding_program
        self.optimization_program = False
        self.global_weak = None
        self.curr_program_contains_disjunction = False
        self.curr_program_contains_aggregates = False
        self.curr_program_contains_choice = False
        self.handle_disjunction = handle_disjunction
        parse_string(encoding_program, lambda stm: (self(stm)))
        self.closed_program()
        
        if not self.global_weak is None and len(self.programs) == 0:
            raise Exception("Only weak program specified - this is not allowed")
        if not self.global_weak is None and self.programs[0].program_type == ProgramQuantifier.FORALL:
            print("WARNING: global weak are ignored when first program is a forall program")
            self.global_weak = None
        if self.programs[len(self.programs)-1].program_type != ProgramQuantifier.CONSTRAINTS:
            self.programs.append(QuantifiedProgram("", [], ProgramQuantifier.CONSTRAINTS, "c", set(), False, False))
        else:
            if self.programs[len(self.programs)-1].contains_choice or self.programs[len(self.programs)-1].contains_disjunction:
                raise Exception("Constraint program cannot contain disjunction of choice rules - it must be stratified")


    def program_contains_weak(self):
        for program in self.programs:
            if program.contains_weak():
                return True
        return False
    
    def program_contains_disjunction(self):
        for program in self.programs:
            if program.contains_disjunction:
                return True
        return False
    
    def program_contains_choice(self):
        for program in self.programs:
            if program.contains_choice:
                return True
        return False

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

    def visit_rule_disj(self, node):
        constraint_body = []
        constraint_body_clone = []
        head  = node.head

        for lit in node.body:
            constraint_body.append(lit)
            pred_name = lit.atom.symbol.name 
            new_funct = clingo.ast.Function(location=node.location, name=f"{pred_name}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}", arguments=lit.atom.symbol.arguments, external=False)
            new_symb = clingo.ast.SymbolicAtom(new_funct)
            new_lit = clingo.ast.Literal(location=node.location, sign=clingo.ast.Sign.NoSign, atom=new_symb)
            constraint_body_clone.append(new_lit)
            if lit.ast_type == clingo.ast.ASTType.Literal and lit.sign == clingo.ast.Sign.NoSign:
                constraint_body_clone.append(lit)
                

        if head.ast_type == clingo.ast.ASTType.Literal:
            if not head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
                negated_head_atom = clingo.ast.Literal(location=node.location, sign=clingo.ast.Sign.Negation, atom=head.atom)
                
                pred_name = head.atom.symbol.name
                new_funct = clingo.ast.Function(location=node.location, name=f"{pred_name}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}", arguments=head.atom.symbol.arguments, external=False)
                new_symb = clingo.ast.SymbolicAtom(new_funct)
                new_lit = clingo.ast.Literal(location=node.location, sign=clingo.ast.Sign.Negation, atom=new_symb)
                constraint_body_clone.append(new_lit)

                constraint_body.append(negated_head_atom)

        elif head.ast_type == clingo.ast.ASTType.Aggregate:
            raise Exception("Choice found in disjunction")
        elif head.ast_type == clingo.ast.ASTType.Disjunction:
            for atom in head.elements:

                pred_name = atom.literal.atom.symbol.name
                new_funct = clingo.ast.Function(location=node.location, name=f"{pred_name}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}", arguments=atom.literal.atom.symbol.arguments, external=False)
                new_symb = clingo.ast.SymbolicAtom(new_funct)
                new_lit = clingo.ast.Literal(location=node.location, sign=clingo.ast.Sign.Negation, atom=new_symb)
                negated_head_atom = clingo.ast.Literal(location=node.location, sign=clingo.ast.Sign.Negation, atom=atom.literal.atom.symbol)

                constraint_body.append(negated_head_atom)
                constraint_body_clone.append(new_lit)
        
        rule_as_constraint = clingo.ast.Rule(location=node.location, head=clingo.ast.BooleanConstant(False), body=constraint_body)
        rule_as_constraint_clone = clingo.ast.Rule(location=node.location, head=clingo.ast.BooleanConstant(False), body=constraint_body_clone)

        self.curr_program_constraints.append(str(rule_as_constraint))
        self.curr_program_constraints_clone.append(str(rule_as_constraint_clone))
        

    def visit_Rule(self, node):
        head = node.head
        rule_is_choice = False
        if head.ast_type == clingo.ast.ASTType.Literal:
            if not head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
                self.extract_predicate_from_literal(head)
        elif head.ast_type == clingo.ast.ASTType.Aggregate:
            self.extract_predicate_from_choice(head)
            self.curr_program_contains_choice = True
            rule_is_choice = True
        elif head.ast_type == clingo.ast.ASTType.Disjunction:
            if not self.handle_disjunction:
                raise Exception("Programs with disjunction must be handled using --disjunction. Only simple ASP programs with disjunction are allowed (not ASP(Q) programs)")
            self.extract_predicate_from_disjunction(head)
            self.curr_program_contains_disjunction = True
        for elem in node.body:
            if elem.atom.ast_type ==  clingo.ast.ASTType.BodyAggregate:
                self.curr_program_contains_aggregates = True
        if not rule_is_choice:
            self.cur_program_rules.append(str(node))
        else:
            self.rewrite_choice_without_guards(node)

        if self.handle_disjunction:
            self.visit_rule_disj(node)
        
        return node.update(**self.visit_children(node))
    
    def rewrite_choice_without_guards(self, choice):
        head = choice.head
        body_vars = dict()

        #find global vars
        for elem in choice.body:
            self.get_variables(elem, body_vars)
        
        aggregate_elements = []
        #construct aggregate elements
        fake_constant = 0
        for el in head.elements:
            elem_vars = dict()
            aggregate_elem_condition = []
            choice_head_atom = el.literal
            self.get_variables(choice_head_atom, elem_vars)
            aggregate_elem_condition.append(choice_head_atom)
            for lit in el.condition:
                aggregate_elem_condition.append(lit)
            agg_vars = []
            for var in elem_vars:
                if not var in body_vars:
                    agg_vars.append(ast.Variable(choice.location, (var)))

            agg_vars.append(ast.Variable(choice.location, choice_head_atom.atom.symbol.name))
            agg_vars = agg_vars if len(agg_vars) > 0 else [ast.Variable(choice.location, str(fake_constant))]
            fake_constant += 1

            agg_element = clingo.ast.BodyAggregateElement(agg_vars, aggregate_elem_condition)
            aggregate_elements.append(agg_element)

        #remap choice rule guards
        constraint_guard_1 = None
        constraint_guard_2 = None
        left_guard = choice.head.left_guard
        right_guard = choice.head.right_guard
        if not left_guard is None:
            self.curr_program_contains_aggregates = True
            remapped_op = self.remap_choice_rule_guards_for_constraint(left_guard.comparison, True)
            constraint_guard_1 = clingo.ast.Guard(remapped_op, left_guard.term)
            agg = clingo.ast.BodyAggregate(choice.location, None, clingo.ast.AggregateFunction.Count, aggregate_elements, constraint_guard_1)
            #construct constraint for left guard
            constraint_body = [l for l in choice.body] + [agg]
            constraint_1 = clingo.ast.Rule(choice.location, clingo.ast.BooleanConstant(False), constraint_body)
            self.cur_program_rules.append(str(constraint_1))
        if not right_guard is None:
            self.curr_program_contains_aggregates = True
            remapped_op = self.remap_choice_rule_guards_for_constraint(right_guard.comparison, False)
            constraint_guard_2 = clingo.ast.Guard(remapped_op, right_guard.term)    
            #construct constraint for right guard
            agg = clingo.ast.BodyAggregate(choice.location, None, clingo.ast.AggregateFunction.Count, aggregate_elements, constraint_guard_2)
            constraint_body = [l for l in choice.body] + [agg]
            constraint_2 = clingo.ast.Rule(choice.location, clingo.ast.BooleanConstant(False), constraint_body)
            self.cur_program_rules.append(str(constraint_2))
 
        #construct free choice
        new_choice_head = ast.Aggregate(choice.location, None, head.elements, None)
        new_choice = ast.Rule(choice.location, new_choice_head, choice.body)
        self.cur_program_rules.append(str(new_choice))



    def get_variables(self, node, body_vars):
        if node.ast_type == ast.ASTType.Variable or node.ast_type == ast.ASTType.SymbolicTerm:
            body_vars[str(node)] = None

        for key in node.keys():
            child = getattr(node, key)
            if isinstance(child, ast.AST):
                self.get_variables(child, body_vars)
            elif isinstance(child, (list, ast.ASTSequence)):
                for item in child:
                    if isinstance(item, ast.AST):
                        self.get_variables(item, body_vars)

    def remap_choice_rule_guards_for_constraint(self, comparison_op, is_left):
        op = None
        if is_left:
            if comparison_op == clingo.ast.ComparisonOperator.Equal:
                op = clingo.ast.ComparisonOperator.NotEqual
            elif comparison_op == clingo.ast.ComparisonOperator.NotEqual:
                op = clingo.ast.ComparisonOperator.Equal
            elif comparison_op == clingo.ast.ComparisonOperator.LessThan:
                op = clingo.ast.ComparisonOperator.LessEqual
            elif comparison_op == clingo.ast.ComparisonOperator.LessEqual:
                op = clingo.ast.ComparisonOperator.LessThan
            elif comparison_op == clingo.ast.ComparisonOperator.GreaterThan:
                op = clingo.ast.ComparisonOperator.GreaterEqual
            elif comparison_op == clingo.ast.ComparisonOperator.GreaterEqual:
                op = clingo.ast.ComparisonOperator.GreaterThan
            else:
                op = clingo.ast.ComparisonOperator.LessEqual
        else:
            if comparison_op == clingo.ast.ComparisonOperator.NotEqual:
                op = clingo.ast.ComparisonOperator.Equal
            elif comparison_op == clingo.ast.ComparisonOperator.Equal:
                op = clingo.ast.ComparisonOperator.NotEqual
            elif comparison_op == clingo.ast.ComparisonOperator.LessThan:
                op = clingo.ast.ComparisonOperator.GreaterEqual
            elif comparison_op == clingo.ast.ComparisonOperator.LessEqual:
                op = clingo.ast.ComparisonOperator.GreaterThan
            elif comparison_op == clingo.ast.ComparisonOperator.GreaterThan:
                op = clingo.ast.ComparisonOperator.LessEqual
            elif comparison_op == clingo.ast.ComparisonOperator.GreaterEqual:
                op = clingo.ast.ComparisonOperator.LessThan
            else:
                op = clingo.ast.ComparisonOperator.GreaterThan
        return op


    def closed_program(self):
        program_str = "\n".join(self.cur_program_rules)
        if self.program_is_open:
            if not re.search(r'fail_\d+|unsat_c', program_str) is None:
                raise Exception("Predicate names and constants of the form fail_\\d+ or unsat_c are not allowed... Exiting")
            if self.curr_program_contains_disjunction and len(self.programs) > 0:
                raise Exception("Only the first program is allowed to contain disjunction")
            if self.cur_program_quantifier == ProgramQuantifier.FORALL and self.curr_program_contains_disjunction:
                raise Exception("Only existential programs may admit disjunction")
            programs_as_constraints_str = "\n".join(self.curr_program_constraints)
            program_as_constraints_str_clone = "\n".join(self.curr_program_constraints_clone)
            program = QuantifiedProgram(program_str, self.curr_weak_constraints, self.cur_program_quantifier, self.curr_program_name, self.head_predicates, self.curr_program_contains_choice, self.curr_program_contains_disjunction, self.curr_program_contains_aggregates, programs_as_constraints_str, program_as_constraints_str_clone)
            if self.cur_program_quantifier != ProgramQuantifier.GLOBAL_WEAK:
                self.programs.append(program)
            else:
                self.global_weak = program
            self.program_is_open = False
        self.cur_program_rules = []
        self.curr_program_constraints = []
        self.curr_program_constraints_clone = []
        self.curr_weak_constraints = []
        self.head_predicates = set()
        self.curr_program_contains_disjunction = False
        self.curr_program_contains_choice = False
        self.curr_program_contains_aggregates = False

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