import clingo
from clingo.ast import parse_string
from .QuantifiedProgram import QuantifiedProgram
import re

class OrUnsatWeakRewriter(clingo.ast.Transformer):
    ANNOTATION_OPEN_P : str = "<<"
    ANNOTATION_CLOSE_P : str = ">>"
    ANNOTATION_OPEN_F : str = ">>"
    ANNOTATION_CLOSE_F : str = "<<"
    program : QuantifiedProgram
    rewritten_program : str
    placeholder_program : str
    placeholder_program_rules : list
    rewrite_predicates : set
    unsat_atom_name : str
    suffix_p_literals : dict
    unsat_literals : dict

    def __init__(self, to_rewrite_predicates, unsat_atom_name, weak_atom_name, weak_atom_level, rewrite_program_predicates, program, negated = True):
        if rewrite_program_predicates:
            self.rewrite_predicates = program.head_predicates | to_rewrite_predicates
        else:
            self.rewrite_predicates = set()
        self.unsat_atom_name_sign = negated
        self.program = program
        self.rewritten_program = ""
        self.placeholder_program = ""
        self.placeholder_program_rules = []
        self.suffix_p_literals = dict()
        self.unsat_literals = dict()
        self.unsat_atom_name = unsat_atom_name
        self.weak_atom_name = weak_atom_name
        self.weak_atom_level = weak_atom_level

    def rewrite(self, suffix_p, iteration):
        if self.placeholder_program == "":
            self.compute_placeholder_program()
        self.rewritten_program = ""
            
        self.rewritten_program = self.placeholder_program
        if not len(self.suffix_p_literals) == 0:
            if not iteration is None:
                self.rewritten_program = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p + str(iteration), self.rewritten_program)
            else:
                self.rewritten_program = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p, self.rewritten_program)
        if not len(self.unsat_literals) == 0:
            if not iteration is None:
                self.rewritten_program = self.pattern_fail.sub(lambda a : self.unsat_literals[a.group(0)] + str(iteration), self.rewritten_program)
            else:
                self.rewritten_program = self.pattern_fail.sub(lambda a : self.unsat_literals[a.group(0)], self.rewritten_program)
        weak_atom_choice = "{" + self.weak_atom_name + suffix_p + str(iteration) + "}."
        self.rewritten_program = f"{self.rewritten_program}\n"

    def visit_Rule(self, node):
        rewritten_body = []
        new_head = node.head
        if not node.head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
            if node.head.ast_type == clingo.ast.ASTType.Literal:
                if node.head.atom.symbol.name in self.rewrite_predicates:
                    self.suffix_p_literals[self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P]  = node.head.atom.symbol.name #self.suffix_p
                    new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)
                    new_head = clingo.ast.SymbolicAtom(new_term)
            else:
                raise Exception("Not supported head")
        else:
            self.suffix_p_literals[self.ANNOTATION_OPEN_P + self.weak_atom_name + self.ANNOTATION_CLOSE_P]  = self.weak_atom_name #self.suffix_p
            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + self.weak_atom_name + self.ANNOTATION_CLOSE_P, [], False)
            new_head = clingo.ast.SymbolicAtom(new_term)
        
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
                                        if condition.atom.symbol.name in self.rewrite_predicates:

                                            self.suffix_p_literals[self.ANNOTATION_OPEN_P + condition.atom.symbol.name + self.ANNOTATION_CLOSE_P] = condition.atom.symbol.name
                                            new_term = clingo.ast.Function(condition.location, self.ANNOTATION_OPEN_P + condition.atom.symbol.name + self.ANNOTATION_CLOSE_P, condition.atom.symbol.arguments, False)
                                            new_atom = clingo.ast.SymbolicAtom(new_term)
                                            new_literal = clingo.ast.Literal(condition.location, condition.sign, new_atom)
                                            new_condition.append(new_literal)
                                        else:
                                            new_condition.append(condition)
                                    else:
                                        raise Exception("Aggregate body atom is None")
                            new_element = clingo.ast.BodyAggregateElement(el.terms, new_condition)
                            new_elements.append(new_element)
                        new_agg = clingo.ast.BodyAggregate(agg.location, agg.left_guard, agg.function, new_elements, agg.right_guard)
                        rewritten_body.append(new_agg)
                    else:
                        #lit is defined in P2
                        if elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom and elem.atom.symbol.name in self.rewrite_predicates:
                            self.suffix_p_literals[self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P] = elem.atom.symbol.name #suffix p
                            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P, elem.atom.symbol.arguments, False)
                            new_atom = clingo.ast.SymbolicAtom(new_term)
                            new_literal = clingo.ast.Literal(node.location, elem.sign, new_atom)
                            rewritten_body.append(new_literal)
                        else:
                            rewritten_body.append(elem)
                else:
                    raise Exception("body atom is None")
            else:
                rewritten_body.append(elem)
        self.unsat_literals[self.ANNOTATION_OPEN_F + self.unsat_atom_name + self.ANNOTATION_CLOSE_F] = self.unsat_atom_name #fail
        fail_func = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.unsat_atom_name + self.ANNOTATION_CLOSE_F, [], False)
        fail_lit = clingo.ast.Literal(node.location, clingo.ast.Sign.Negation if self.unsat_atom_name_sign else clingo.ast.Sign.NoSign, clingo.ast.SymbolicAtom(fail_func))
        rewritten_body.append(fail_lit)

        self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head, rewritten_body)))

    def compute_placeholder_program(self):
        if self.placeholder_program != "":
            return
        self.placeholder_program_rules = []
        parse_string(self.program.rules, lambda stm: (self(stm)))
        self.placeholder_program = "\n".join(self.placeholder_program_rules)
        self.placeholder_program_rules = []
        self.pattern_suffix_p = re.compile('|'.join(re.escape(k) for k in self.suffix_p_literals))
        self.pattern_fail = re.compile('|'.join(re.escape(k) for k in self.unsat_literals))