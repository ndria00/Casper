import clingo
import re

from .SolverSettings import SolverSettings
from .WeakConstraint import WeakConstraint
from .OrProgramRewriter import OrProgramRewriter
from .QuantifiedProgram import QuantifiedProgram
from clingo.ast import parse_string

class CostRewriter(clingo.ast.Transformer):
    
    ANNOTATION_OPEN : str = "<<"
    ANNOTATION_CLOSE : str = ">>"

    LEVEL_VARIABLE : str = "L"
    WEIGHT_VARIABLE : str = "W"
    COST_VARIABLE : str = "C"
    VIOLATION_TERMS_VARIABLES_PREFIX : str = "X_"
    
    program : QuantifiedProgram
    #placeholder for rules v(C,L,X) :- B_r. for each weak in program
    placeholder_violation_rules : list
    placeholder_violation_program : str
    level_placeholder_rules : list
    level_placeholder_program : str
    violation_predicates_arities : dict
    #cost_at_level(C, L) :- level(L), #sum{C,L:v(C,L,X_1);C,L:v(C,L,X_2);}
    placeholder_aggregate_rule : str
    cost_predicate : str
    violation_predicate : str
    level_predicate : str
    rewritten_program : str
    annotated_literals: dict
    rewritten_program_head_predicates : set
    current_weak : WeakConstraint
    current_violation_predicate : str
    last_rewriting_suffix : str
    rewrite_level_predicate : bool

    def __init__(self, program, violation_predicate=SolverSettings.WEAK_VIOLATION_ATOM_NAME, level_predicate=SolverSettings.LEVEL_COST_ATOM_NAME, cost_predicate=SolverSettings.COST_AT_LEVEL_ATOM_NAME, keep_body_signature=False, rewrite_level_predicate=True):
        self.program = program
        self.cost_predicate = cost_predicate
        self.placeholder_violation_rules = []
        self.placeholder_violation_program = ""
        self.violation_predicate = violation_predicate
        self.rewritten_program = ""
        self.annotated_literals = dict()
        self.rewritten_program_head_predicates = set()
        self.current_violation_predicate = ""
        self.keep_body_signature = keep_body_signature
        self.violation_predicates_arities = dict()
        self.last_rewriting_suffix = ""
        self.level_placeholder_rules = []
        self.level_placeholder_program = ""
        self.level_predicate = level_predicate
        self.placeholder_aggregate_rule = ""
        self.rewrite_level_predicate = rewrite_level_predicate

    def rewrite(self, suffix=""):
        self.current_violation_predicate = f"{self.violation_predicate}{suffix}"
        self.current_cost_predicate = f"{self.cost_predicate}{suffix}"
        self.current_level_predicate = f"{self.level_predicate}{suffix}"
        if self.placeholder_violation_program == "":
            self.compute_placeholder_program()
            self.pattern_annotated_literals = re.compile('|'.join(re.escape(k) for k in self.annotated_literals))
        self.rewritten_program = ""
        self.rewritten_program_head_predicates = set([self.current_violation_predicate])
        self.rewritten_program_head_predicates_with_levels_and_aggregate = set([self.current_violation_predicate, self.current_level_predicate, self.current_cost_predicate])
        self.rewritten_program = self.pattern_annotated_literals.sub(lambda a : self.annotated_literals[a.group(0)] + suffix, self.placeholder_violation_program)
        self.last_rewriting_suffix = suffix

    def visit_Minimize(self, node):
        rewritten_body = []
        for elem in node.body:
            if elem.ast_type == clingo.ast.ASTType.Literal:
                if not elem.atom is None:
                    if elem.atom.ast_type == clingo.ast.ASTType.BodyAggregate:
                        agg = elem.atom
                        new_elements = []
                        for el in agg.elements:
                            new_condition = []
                            for condition in el.condition:
                                if condition.ast_type == clingo.ast.ASTType.Literal:
                                    if not condition.atom is None:
                                        if condition.atom.symbol.name in self.program.head_predicates and not self.keep_body_signature:
                                            self.annotated_literals[self.ANNOTATION_OPEN + condition.atom.symbol.name + self.ANNOTATION_CLOSE] = condition.atom.symbol.name
                                            new_term = clingo.ast.Function(condition.location, self.ANNOTATION_OPEN + condition.atom.symbol.name + self.ANNOTATION_CLOSE)
                                            new_atom = clingo.ast.SymbolicAtom(new_term)
                                            new_literal = clingo.ast.Literal(condition.location, condition.sign, new_atom)
                                            new_condition.append(new_literal)
                                        else:
                                            new_condition.append(condition)    
                                    else:
                                        raise Exception("body atom is None")
                                else:
                                    new_condition.append(condition)
                            new_element = clingo.ast.BodyAggregateElement(el.terms, new_condition)
                            new_elements.append(new_element)
                        new_agg = clingo.ast.BodyAggregate(elem.location, agg.left_guard, agg.function, new_elements, agg.right_guard)
                        rewritten_body.append(new_agg)
                    #lit is defined in P2
                    elif elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom:
                        if elem.atom.symbol.name in self.program.head_predicates and not self.keep_body_signature:
                            self.annotated_literals[self.ANNOTATION_OPEN + elem.atom.symbol.name + self.ANNOTATION_CLOSE] = elem.atom.symbol.name
                            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN + elem.atom.symbol.name + self.ANNOTATION_CLOSE, elem.atom.symbol.arguments, False)
                            new_atom = clingo.ast.SymbolicAtom(new_term)
                            new_literal = clingo.ast.Literal(node.location, elem.sign, new_atom)
                            rewritten_body.append(new_literal)
                        else:
                            rewritten_body.append(elem)                          
                    else:
                        rewritten_body.append(elem)
                else:
                    raise Exception("body atom is None")
            else:
                rewritten_body.append(elem)
        #original weak
        body_repr = ", ".join(str(lit) for lit in rewritten_body)
        violation_rule = f"{self.current_weak_head}:-{body_repr}."
        if self.rewrite_level_predicate:
            level_rule = f"{self.ANNOTATION_OPEN}{self.level_predicate}{self.ANNOTATION_CLOSE}({self.current_weak_level}):-{self.current_weak_head}."
        else:
            level_rule = f"{self.level_predicate}({self.current_weak_level}):-{self.current_weak_head}."
            
        self.level_placeholder_rules.append(level_rule)
        self.placeholder_violation_rules.append(str(violation_rule))
        

    def compute_placeholder_program(self):

        self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}"] = self.violation_predicate
        self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.cost_predicate}{self.ANNOTATION_CLOSE}"] = self.cost_predicate
        if self.rewrite_level_predicate:
            self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.level_predicate}{self.ANNOTATION_CLOSE}"] = self.level_predicate

        for weak in self.program.weak_constraints:
            #construct head of violation rule
            terms_str = ",".join(weak.terms)
            self.current_weak_head = ""
            self.current_weak_level = self.LEVEL_VARIABLE if weak.is_level_variable() else weak.level
            aggregate_lits = []
            violation_atom_arity = 0
            if len(weak.terms) > 0:
                self.current_weak_head = f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}({weak.weight},{self.current_weak_level},{terms_str})"
                violation_atom_arity = 2 + len(weak.terms)
            else:
                self.current_weak_head = f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}({weak.weight},{self.current_weak_level})"
                violation_atom_arity = 2
            if not violation_atom_arity in self.violation_predicates_arities:
                self.violation_predicates_arities[violation_atom_arity] = None
            #construct violation rules
            self.current_weak = str(weak)
            parse_string(self.current_weak, lambda stm: (self(stm)))

        if len(self.violation_predicates_arities) > 0:
            for arity in self.violation_predicates_arities:
                annotated_violation_atom = self.ANNOTATION_OPEN + self.violation_predicate + self.ANNOTATION_CLOSE
                self.annotated_literals[annotated_violation_atom] = self.violation_predicate
                aggregate_terms = [self.WEIGHT_VARIABLE, self.LEVEL_VARIABLE] + [f"{self.VIOLATION_TERMS_VARIABLES_PREFIX}{i}" for i in range(2, arity)]
                if len(aggregate_terms) > 2:
                    violation_atom_aggregate = self.WEIGHT_VARIABLE + "," + ",".join(aggregate_terms[2:]) + " : " + annotated_violation_atom + "(" + ",".join(aggregate_terms) + ")"
                else:#len is exactly 2 (i.e., [C,L])
                    violation_atom_aggregate = self.WEIGHT_VARIABLE + " : " + annotated_violation_atom + "(" + ",".join(aggregate_terms) + ")"
                aggregate_lits.append(violation_atom_aggregate)
            

        aggregate = "; ".join(aggregate_lits)
        if self.rewrite_level_predicate:
            aggregate_rule_body = self.ANNOTATION_OPEN + self.level_predicate + self.ANNOTATION_CLOSE + "(" + self.LEVEL_VARIABLE + "),  #sum{ " + aggregate + "}"
        else:
            aggregate_rule_body = self.level_predicate + "(" + self.LEVEL_VARIABLE + "),  #sum{ " + aggregate + "}"
        annotated_cost_at_level_predicate = self.ANNOTATION_OPEN +  self.cost_predicate + self.ANNOTATION_CLOSE
        aggregate_rule_head = f"{annotated_cost_at_level_predicate}({self.COST_VARIABLE}, {self.LEVEL_VARIABLE})"
        self.annotated_literals[annotated_cost_at_level_predicate] = self.cost_predicate

        self.placeholder_aggregate_rule = f"{aggregate_rule_head}:-{aggregate_rule_body}={self.COST_VARIABLE}."
        self.placeholder_violation_program = "\n".join(self.placeholder_violation_rules)
        self.level_placeholder_program = "\n".join(self.level_placeholder_rules)
        

    def rewritten_program_with_aggregate_and_levels(self):
        if self.placeholder_violation_program != "":
            rewritten_levels = self.pattern_annotated_literals.sub(lambda a : self.annotated_literals[a.group(0)] + self.last_rewriting_suffix, self.level_placeholder_program)
            rewritten_cost = self.pattern_annotated_literals.sub(lambda a : self.annotated_literals[a.group(0)] + self.last_rewriting_suffix, self.placeholder_aggregate_rule)
            
            return f"{rewritten_levels}\n{self.rewritten_program}\n{rewritten_cost}"
        return ""
    