
import clingo

from .ConstraintProgramRewriter import ConstraintProgramRewriter
from .MyProgram import MyProgram
from clingo.ast import parse_string
import re

class RefinementRewriter(clingo.ast.Transformer):
    ANNOTATION_OPEN_P : str = '-'
    ANNOTATION_CLOSE_P : str = '-'
    ANNOTATION_OPEN_N : str = '<'
    ANNOTATION_CLOSE_N : str = '>'
    ANNOTATION_OPEN_F : str = '>'
    ANNOTATION_CLOSE_F : str = '<'
    original_programs_list : list
    placeholder_programs_list : list
    rewritten_programs_list : list
    constraint_prorgam_rewriter : ConstraintProgramRewriter
    suffix_p : str
    suffix_n : str
    suffix_p_literals : dict
    suffix_n_literals : dict
    fail_literals : dict
    fail_atom_name : str
    ground_transformation : bool
    rewritten_program : str
    parsing_original_program: bool

    def __init__(self, original_programs, ground_transformation):
        self.original_programs_list = original_programs
        self.placeholder_programs_list = ["" for _ in range(len(self.original_programs_list))]
        self.rewritten_programs_list = ["" for _ in range(len(self.original_programs_list))]
        self.ground_transformation = ground_transformation
        self.suffix_p = ""
        self.suffix_n = ""
        self.fail_atom_name = ""
        self.suffix_p_literals = dict()
        self.suffix_n_literals = dict()
        self.fail_literals = dict()
        to_rewrite_in_constraint_predicates = set()
        #refineme
        for i in range(len(self.original_programs_list)-1):
            to_rewrite_in_constraint_predicates = to_rewrite_in_constraint_predicates | self.original_programs_list[i].head_predicates
        self.constraint_program_rewriter = ConstraintProgramRewriter(to_rewrite_in_constraint_predicates, self.original_programs_list[-1])
        
        self.rewritten_program = ""
        self.fail_atom_name = f"fail_"
        self.parsing_original_program = False
        
    def replace_or_simplify(self, m):
        #matches are of the form not <pred_name>
        pred_name = m.group(0)[5:len(m.group(0))-1]
        if pred_name in self.model_symbols_set:
            self.erase_rule = True
        return ""

    def rewrite(self, model, iteration):
        self.suffix_p = f"_p_{iteration}"
        self.suffix_n = f"_n_{iteration}"
        self.rewritten_program = ""
                
        for i in range(len(self.original_programs_list)-1):
                self.rewritten_programs_list[i] = self.placeholder_programs_list[i]
        fail_atom_name = "fail_" + str(iteration)
        self.constraint_program_rewriter.rewrite(self.suffix_p, fail_atom_name, iteration)
        self.rewritten_programs_list[-1] = self.constraint_program_rewriter.rewritten_program
        if not self.ground_transformation:
            for i in range(len(self.original_programs_list)):
                self.rewritten_programs_list[i] = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + self.suffix_p, self.rewritten_programs_list[i])
                self.rewritten_programs_list[i] = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + self.suffix_n, self.rewritten_programs_list[i])
                self.rewritten_programs_list[i] = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), self.rewritten_programs_list[i])

        else:
            raise Exception("Not implemented")
        #     #TODO this is a prototype. Update to work with ground non-propositional programs
        #     self.rewritten_program  = self.placeholder_program.split("\n")
        #     self.model_symbols_set = set()
        #     for model in models:
        #         for symbol in model:
        #             self.model_symbols_set.add(str(symbol))
        #     for i in range(len(self.rewritten_program)):
        #         self.rewritten_program[i] = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + self.suffix_p, self.rewritten_program[i])
        #         self.erase_rule = False
            
        #         self.rewritten_program[i] = self.pattern_suffix_n_negated.sub(self.replace_or_simplify, self.rewritten_program[i])                
        #         #rule has some negative literal false in in the model
        #         if self.erase_rule:
        #            self.rewritten_program[i] = ""
        #         else:
        #             #no negative false literal in the body - just clear the rule from remaining chars
        #             #remove extra chars remained after sub
        #             self.rewritten_program[i] = self.rewritten_program[i].replace(" ;", "")
        #             self.rewritten_program[i] = self.rewritten_program[i].replace("; .", ".")
                    
        #         self.rewritten_program[i] = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + self.suffix_n, self.rewritten_program[i])
        #         self.rewritten_program[i] = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), self.rewritten_program[i])

        #     self.rewritten_program = "\n".join(self.rewritten_program)   
        counterexample_facts = ""
        for symbol in model:
            if symbol.name in self.original_programs_list[0].head_predicates:
                new_symbol = clingo.Function(symbol.name + self.suffix_n, symbol.arguments, symbol.positive)
                counterexample_facts = counterexample_facts + str(new_symbol) + "."
        
        self.rewritten_programs_list[0] += counterexample_facts
        self.rewritten_program += self.constraint_program_rewriter.rewritten_program
        self.rewritten_program = "\n".join(self.rewritten_programs_list)
        self.rewritten_program += counterexample_facts
        
        
    def visit_Rule(self, node):
        rewritten_body = []
        new_head = None
        for elem in node.body:
            if elem.ast_type == clingo.ast.ASTType.Literal:
                if not elem.atom is None:
                    if elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom and elem.atom.symbol.name in self.original_programs_list[0].head_predicates:
                                        #only on the first program I am doing the reduct. In the remaining programs I only use the + signature
                        if elem.sign and self.parsing_original_program:
                            self.suffix_n_literals[self.ANNOTATION_OPEN_N + elem.atom.symbol.name + self.ANNOTATION_CLOSE_N] = elem.atom.symbol.name #self.suffix_n
                            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_N + elem.atom.symbol.name + self.ANNOTATION_CLOSE_N, elem.atom.symbol.arguments, False)
                        else:
                            self.suffix_p_literals[self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P] = elem.atom.symbol.name #self.suffix_p
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
                
        #disable all programs after the program for which I compute the reduct
        if not self.parsing_original_program:
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name #fail
            fail_func = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            fail_lit = clingo.ast.Literal(node.location, clingo.ast.Sign.Negation, clingo.ast.SymbolicAtom(fail_func))
            rewritten_body.append(fail_lit)

        if node.head.atom.ast_type != clingo.ast.ASTType.BooleanConstant:
            try:
                self.suffix_p_literals[self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P] = node.head.atom.symbol.name #self.suffix_p 
                new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)
                new_head = clingo.ast.SymbolicAtom(new_term)
                #add fail :- a_p not a_n for every rule in P2
                f_1 = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)

                self.suffix_n_literals[self.ANNOTATION_OPEN_N + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_N] = node.head.atom.symbol.name #self.suffix_n
                f_2 = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_N + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_N, node.head.atom.symbol.arguments, False)
                l_1 = clingo.ast.Literal(node.location, False, f_1)
                l_2 = clingo.ast.Literal(node.location, True, f_2)
                self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
                fail_head = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
                fail_body = [l_1, l_2]
                self.rewritten_program = self.rewritten_program + str(clingo.ast.Rule(node.location, fail_head, fail_body)) + "\n"
                nl_1 = clingo.ast.Literal(node.location, True, f_1)
                nl_2 = clingo.ast.Literal(node.location, False, f_2)
                fail_body = [nl_1, nl_2]
                self.rewritten_program = self.rewritten_program + str(clingo.ast.Rule(node.location, fail_head, fail_body)) + "\n"
            except:
                print("Usupported head")
                exit(1)
        else: 
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            new_head = clingo.ast.SymbolicAtom(new_term)
        
        self.rewritten_program = self.rewritten_program + str(clingo.ast.Rule(node.location, new_head, rewritten_body)) + "\n"
    


    def compute_placeholder_program(self):
        self.constraint_program_rewriter.compute_placeholder_program()
        #do not parse also constraint program - it will be treated separately
        for i in range(len(self.original_programs_list)-1):
            program = self.original_programs_list[i]
            self.parsing_original_program = True if i == 0 else False

            parse_string("\n".join(program.rules), lambda stm: (self(stm)))
            self.rewritten_programs_list[i] = self.rewritten_program
            self.rewritten_program = ""

        self.pattern_suffix_p = re.compile('|'.join(re.escape(k) for k in self.suffix_p_literals))
        self.pattern_suffix_n = re.compile('|'.join(re.escape(k) for k in self.suffix_n_literals))
        self.pattern_fail = re.compile('|'.join(re.escape(k) for k in self.fail_literals))
        #one rule per list elem
        if self.ground_transformation:
            self.pattern_suffix_n_negated = re.compile('not ' + '|not '.join(re.escape(k) for k in self.suffix_n_literals))
        #print("Placeholder program: ", self.placeholder_program)
        for i in range(len(self.original_programs_list)-1):
            self.placeholder_programs_list[i] = self.rewritten_programs_list[i]
        self.placeholder_programs_list[len(self.placeholder_programs_list)-1] = self.constraint_program_rewriter.rewritten_program 