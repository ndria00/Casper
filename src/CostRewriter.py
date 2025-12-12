import clingo
import re

from .WeakConstraint import WeakConstraint
from .OrProgramRewriter import OrProgramRewriter
from .QuantifiedProgram import QuantifiedProgram
from clingo.ast import parse_string

class CostRewriter(clingo.ast.Transformer):
    
    ANNOTATION_OPEN : str = "<<"
    ANNOTATION_CLOSE : str = ">>"
    
    program : QuantifiedProgram
    placeholder_program_rules : list
    placeholder_program : str
    cost_predicate : str
    violation_predicate : str
    level_predicate : str
    level_to_aggregate_lits : dict
    level_facts : set
    rewritten_program : str
    annotated_literals: dict
    rewritten_program_head_predicates : set
    current_weak : WeakConstraint
    current_violation_predicate : str

    def __init__(self, program, level_predicate, violation_predicate, cost_predicate):
        self.program = program
        self.cost_predicate = cost_predicate
        self.placeholder_program = ""
        self.placeholder_program_rules = []
        self.level_predicate = level_predicate
        self.violation_predicate = violation_predicate
        self.rewritten_program = ""
        self.level_facts = set()
        self.level_to_aggregate_lits = dict()
        self.annotated_literals = dict()
        self.rewritten_program_head_predicates = set()
        self.current_violation_predicate = ""

    def rewrite(self, suffix=""):
        self.current_violation_predicate = f"{self.violation_predicate}{suffix}"
        if self.placeholder_program == "":
            self.compute_placeholder_program()
            self.pattern_annotated_literals = re.compile('|'.join(re.escape(k) for k in self.annotated_literals))
        self.rewritten_program = ""
        self.rewritten_program_head_predicates = set([f"{self.cost_predicate}{suffix}", f"{self.current_violation_predicate}", f"{self.level_predicate}{suffix}"])

        self.rewritten_program = self.pattern_annotated_literals.sub(lambda a : self.annotated_literals[a.group(0)] + suffix, self.placeholder_program)

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
                                        if condition.atom.symbol.name in self.program.head_predicates:
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
                        if elem.atom.symbol.name in self.program.head_predicates:
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
        self.placeholder_program_rules.append(str(violation_rule))


    def compute_placeholder_program(self):
        self.placeholder_constraint = ""

        self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}"] = self.violation_predicate
        self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.cost_predicate}{self.ANNOTATION_CLOSE}"] = self.cost_predicate
        self.annotated_literals[f"{self.ANNOTATION_OPEN}{self.level_predicate}{self.ANNOTATION_CLOSE}"] = self.level_predicate

        for weak in self.program.weak_constraints:
            #construct head of violation rule
            terms = ",".join(weak.terms)
            self.current_weak_head = ""
            aggregate_lit = ""
            if len(weak.terms) > 0:
                self.current_weak_head = f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}({weak.weight},{weak.level},{terms})"
                aggregate_lit = f"{weak.weight},{weak.level},{terms}:{self.current_weak_head}"
            else:
                self.current_weak_head = f"{self.ANNOTATION_OPEN}{self.violation_predicate}{self.ANNOTATION_CLOSE}({weak.weight},{weak.level})"
                aggregate_lit = f"{weak.weight},{weak.level}:{self.current_weak_head}"
            self.level_facts.add(weak.level)

            
            #aggregate lits that will be part of the multi aggregate for a given level
            if not weak.level in self.level_to_aggregate_lits:
                self.level_to_aggregate_lits[weak.level] = []

            self.level_to_aggregate_lits[weak.level].append(aggregate_lit)
            
            #construct violation rules
            self.current_weak = str(weak)
            parse_string(self.current_weak, lambda stm: (self(stm)))
    
            #construct rule with aggregates
            
        for weak_level in self.level_facts:
            aggregate_body = ";".join(self.level_to_aggregate_lits[weak_level])
            aggregate = "#sum{" +  aggregate_body + "}=C"
            self.placeholder_program_rules.append(f"{self.ANNOTATION_OPEN}level{self.ANNOTATION_CLOSE}({weak_level}).")
            self.placeholder_program_rules.append(f"{self.ANNOTATION_OPEN}{self.cost_predicate}{self.ANNOTATION_CLOSE}(C,{weak_level}):-{self.ANNOTATION_OPEN}level{self.ANNOTATION_CLOSE}({weak_level}),{aggregate}.")
        self.placeholder_program = "\n".join(self.placeholder_program_rules)