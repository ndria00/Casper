import clingo
from clingo.ast import parse_string
from .QuantifiedProgram import QuantifiedProgram
import re

class ConstraintProgramRewriter(clingo.ast.Transformer):
    ANNOTATION_OPEN_P : str = "<<"
    ANNOTATION_CLOSE_P : str = ">>"
    ANNOTATION_OPEN_F : str = ">>"
    ANNOTATION_CLOSE_F : str = "<<"
    constraints_program : QuantifiedProgram
    rewritten_program : str
    placeholder_program : str
    placeholder_program_rules : list
    rewrite_predicates : set
    fail_atom_name : str
    suffix_p_literals : dict
    fail_literals : dict

    def __init__(self, to_rewrite_predicates, constraints_program):
        self.rewrite_predicates = constraints_program.head_predicates | to_rewrite_predicates
        self.constraints_program = constraints_program
        self.rewritten_program = ""
        self.placeholder_program = ""
        self.placeholder_program_rules = []
        self.suffix_p_literals = dict()
        self.fail_literals = dict()

    def rewrite(self, suffix_p, fail_atom_name, iteration):
        self.rewritten_program = ""
        self.fail_atom_name = fail_atom_name
            
        self.rewritten_program = self.placeholder_program
        if not len(self.suffix_p_literals) == 0:
            self.rewritten_program = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p, self.rewritten_program)
        if not len(self.fail_literals) == 0:
            self.rewritten_program = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), self.rewritten_program) 

    def visit_Rule(self, node):
        rewritten_body = []
        if node.head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
            new_head = node.head
        else:
            if node.head.ast_type == clingo.ast.ASTType.Literal:
                self.suffix_p_literals[self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P]  = node.head.atom.symbol.name #self.suffix_p
                new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)
                new_head = clingo.ast.SymbolicAtom(new_term)
            else:
                raise Exception("Not supported head")

        for elem in node.body:
            if elem.ast_type == clingo.ast.ASTType.Literal:
                if not elem.atom is None:
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
        self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name #fail
        fail_func = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
        fail_lit = clingo.ast.Literal(node.location, clingo.ast.Sign.Negation, clingo.ast.SymbolicAtom(fail_func))
        rewritten_body.append(fail_lit)

        self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head, rewritten_body)))

    def compute_placeholder_program(self):
        if self.placeholder_program != "":
            return
        self.fail_atom_name = "fail_"
        self.placeholder_program_rules = []
        parse_string(self.constraints_program.rules, lambda stm: (self(stm)))
        self.placeholder_program = "\n".join(self.placeholder_program_rules)
        self.placeholder_program_rules = []
        self.pattern_suffix_p = re.compile('|'.join(re.escape(k) for k in self.suffix_p_literals))
        self.pattern_fail = re.compile('|'.join(re.escape(k) for k in self.fail_literals))