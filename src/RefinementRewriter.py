
import copy
import clingo

from .ConstraintProgramRewriter import ConstraintProgramRewriter
from .MyProgram import MyProgram, ProgramQuantifier
from clingo.ast import parse_string
import re

#Takes P_2, ..., P_n : C as programs
#flips quantifiers and constraint if the first program is \forall (i.e. the outermost program was a \exists)
#the first two programs collapse into a single ASP program
class RefinementRewriter(clingo.ast.Transformer):
    ANNOTATION_OPEN_P : str = '-'
    ANNOTATION_CLOSE_P : str = '-'
    ANNOTATION_OPEN_N : str = '<'
    ANNOTATION_CLOSE_N : str = '>'
    ANNOTATION_OPEN_F : str = '>'
    ANNOTATION_CLOSE_F : str = '<'
    original_programs_list : list
    placeholder_programs_list_rules : list
    rewritten_programs_list : list
    rewritten_programs_list_rules : list
    constraint_program_rewriter : ConstraintProgramRewriter
    suffix_p : str
    suffix_n : str
    suffix_p_literals : dict
    suffix_n_literals : dict
    fail_literals : dict
    fail_atom_name : str
    ground_transformation : bool
    placeholder_program : str
    parsing_first_program: bool
    to_rewrite_predicates : set

    def __init__(self, original_programs, prorgam_c, program_neg_c, ground_transformation):
        self.original_programs_list = original_programs
        self.placeholder_programs_list_rules = []
        self.rewritten_programs_list_rules = ["" for _ in range(len(self.original_programs_list))]
        self.rewritten_programs_list = []
        self.ground_transformation = ground_transformation
        self.suffix_p = ""
        self.suffix_n = ""
        self.fail_atom_name = ""
        self.suffix_p_literals = dict()
        self.suffix_n_literals = dict()
        self.fail_literals = dict()
        #flip constraint if the first program to rewrite is an exists (e.g, the first program of the ASPQ is quantified universally) 
        if self.original_programs_list[0].program_type == ProgramQuantifier.EXISTS:
            self.original_programs_list.append(program_neg_c)
        else:
            self.original_programs_list.append(prorgam_c)
        self.to_rewrite_predicates = set()
        #refine
        for i in range(len(self.original_programs_list)-1):
            self.to_rewrite_predicates = self.to_rewrite_predicates | self.original_programs_list[i].head_predicates
        self.to_rewrite_predicates = self.to_rewrite_predicates | self.original_programs_list[-1].head_predicates
        self.constraint_program_rewriter = ConstraintProgramRewriter(self.to_rewrite_predicates, self.original_programs_list[-1])

        self.fail_atom_name = f"fail_"
        self.parsing_first_program = False
        
    def replace_or_simplify(self, m):
        #matches are of the form not <pred_name>
        pred_name = m.group(0)[5:len(m.group(0))-1]
        if pred_name in self.model_symbols_set:
            self.erase_rule = True
        return ""

    def rewrite(self, counterexample, iteration):
        self.rewritten_programs_list = []
        self.suffix_p = f"_p_{iteration}"
        self.suffix_n = f"_n_{iteration}"
                
        fail_atom_name = "fail_" + str(iteration)
        #rewrite constraint
        self.constraint_program_rewriter.rewrite(self.suffix_p, fail_atom_name, iteration)
        for i in range(len(self.original_programs_list) -1):
            self.rewritten_programs_list_rules[i] = self.placeholder_programs_list_rules[i]
            if not self.ground_transformation:
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + self.suffix_p, self.rewritten_programs_list_rules[i])
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + self.suffix_n, self.rewritten_programs_list_rules[i])
                self.rewritten_programs_list_rules[i] = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), self.rewritten_programs_list_rules[i])
            else:
                #TODO this is a prototype. Update to work with ground non-propositional programs
                self.rewritten_program  = []
                self.model_symbols_set = set()
                for symbol in counterexample:
                    self.model_symbols_set.add(str(symbol))

                for rule in self.placeholder_programs_list_rules[i]:
                    self.erase_rule = False
                    #replace suffix_n
                    rule = self.pattern_suffix_n_negated.sub(self.replace_or_simplify, rule)

                    #if false negated literal in rule ignore, otherwise replace suffix_p
                    if not self.erase_rule:
                        rule = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + self.suffix_n, rule)
                        rule = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + self.suffix_p, rule)
                        #no negative false literal in the body - just clear the rule from remaining chars
                        #remove extra chars remained after sub
                        rule = rule.replace(" ;", "")
                        rule = rule.replace("; .", ".")
                        rule = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), rule)
                        self.rewritten_program.append(rule)

                self.rewritten_programs_list_rules[i] = "\n".join(self.rewritten_program)

            prg_name = self.original_programs_list[i].name
            #flip quantifiers if the first program is \forall (i.e. the outermost program was an \exists)
            quantifier = None
            if self.original_programs_list[0].forall():
                quantifier = self.original_programs_list[i].program_type
            else:
                quantifier = ProgramQuantifier.EXISTS if self.original_programs_list[i].program_type == ProgramQuantifier.FORALL else ProgramQuantifier.FORALL
            
            rewritten_preds = set()
            for pred in self.original_programs_list[i].head_predicates:
                rewritten_preds.add(f"{pred}{self.suffix_p}")

            self.rewritten_programs_list.append(MyProgram(self.rewritten_programs_list_rules[i], quantifier, prg_name, rewritten_preds))
           
        #add rewritten constraint program
        prg_name = self.original_programs_list[-1].name
        rewritten_preds = set()
        for pred in self.original_programs_list[-1].head_predicates:
            rewritten_preds.add(f"{pred}{self.suffix_p}")
        self.rewritten_programs_list.append(MyProgram(self.constraint_program_rewriter.rewritten_program, ProgramQuantifier.CONSTRAINTS, prg_name, rewritten_preds))
        
           
        self.counterexample_facts = " "
        for symbol in counterexample:
            #symbol predicate in P_2
            if symbol.name in self.original_programs_list[0].head_predicates:
                new_symbol = clingo.Function(symbol.name + self.suffix_n, symbol.arguments, symbol.positive)
                self.counterexample_facts = self.counterexample_facts + str(new_symbol) + "."

        #add fail atom as an head predicate (it might be needed by rewritings of subsequent ASPQ programs)
        self.rewritten_programs_list[0].head_predicates.add(fail_atom_name)
        #add counterexample facts in the first exists program
        self.rewritten_programs_list[0].rules += self.counterexample_facts
        
        
    #called from outside only when the refinement becomes an ASP program
    def refined_program(self):
        #collapse the first three programs into an exists program and rename the remaining ones
        if len(self.original_programs_list) > 3:
            refinement_aspq = []
            refinement_str = ""
            head_predicates = set()

            for i in range(2):
                refinement_str += self.rewritten_programs_list[i].rules
                head_predicates = head_predicates | self.rewritten_programs_list[i].head_predicates

            refinement_aspq.append(MyProgram(refinement_str, ProgramQuantifier.EXISTS, "1", head_predicates))
            
            for i in range(2, len(self.rewritten_programs_list)):
                #the third program has name 4 since 1 is not in the original list
                self.rewritten_programs_list[i].name = str(i-3)
                refinement_aspq.append(self.rewritten_programs_list[i])
            return refinement_aspq
        else:#refinement is a single exists program and just the textual representation in enough - no need to build an ASPQ solver for it
            refinement_str = ""
            #collapse the first three quantifiers into an exists quantifier and leave the rest of the program unchanged
            for program in self.rewritten_programs_list:
                refinement_str += program.rules
            refinement_str += self.counterexample_facts
            return refinement_str

    def visit_Rule(self, node):
        rewritten_body = []
        new_head = None
        for elem in node.body:
            if elem.ast_type == clingo.ast.ASTType.Literal:
                if not elem.atom is None:
                    #predicates of the first program are rewritten over the + and - signature for mimicking the reduct 
                    #predicates of the remaining programs must be written over a new signature (possibly just the + signature)
                    #for making each refinement to have independent chains of ASP programs
                    if elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom:
                        #parsing programs after the first program (the one on which the refinement produces the reduct)
                        if not self.parsing_first_program:
                            #if predicate is defined in some program rewrite it on the + signature, otherwise leave it unchanged
                            if elem.atom.symbol.name in self.to_rewrite_predicates:
                                self.suffix_p_literals[self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P] = elem.atom.symbol.name #self.suffix_p
                                new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P, elem.atom.symbol.arguments, False)                                
                                new_atom = clingo.ast.SymbolicAtom(new_term)
                                new_literal = clingo.ast.Literal(node.location, elem.sign, new_atom)
                                rewritten_body.append(new_literal)
                            else:
                                rewritten_body.append(elem)
                        else:
                            #parsing first program
                            #if predicate is defined in the program for which I am writing the reduct, map it to the + and - signatures
                            if elem.atom.symbol.name in self.original_programs_list[0].head_predicates:
                                if elem.sign:
                                    self.suffix_n_literals[self.ANNOTATION_OPEN_N + elem.atom.symbol.name + self.ANNOTATION_CLOSE_N] = elem.atom.symbol.name #self.suffix_n
                                    new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_N + elem.atom.symbol.name + self.ANNOTATION_CLOSE_N, elem.atom.symbol.arguments, False)
                                else:
                                    self.suffix_p_literals[self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P] = elem.atom.symbol.name #self.suffix_p
                                    new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + elem.atom.symbol.name + self.ANNOTATION_CLOSE_P, elem.atom.symbol.arguments, False)

                                new_atom = clingo.ast.SymbolicAtom(new_term)
                                new_literal = clingo.ast.Literal(node.location, elem.sign, new_atom)
                                rewritten_body.append(new_literal)
                            else:#if predicate is not defined in the program for which I am writing the reduct, leave it as it is
                                rewritten_body.append(elem)
                    else:
                        rewritten_body.append(elem)
                else:
                    raise Exception("body atom is None")    
            else:
                rewritten_body.append(elem)
                
        #disable all programs after the program for which I compute the reduct
        if not self.parsing_first_program:
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name #fail
            fail_func = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            fail_lit = clingo.ast.Literal(node.location, clingo.ast.Sign.Negation, clingo.ast.SymbolicAtom(fail_func))
            rewritten_body.append(fail_lit)

        if node.head.atom.ast_type != clingo.ast.ASTType.BooleanConstant:
            self.suffix_p_literals[self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P] = node.head.atom.symbol.name #self.suffix_p 
            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)
            new_head = clingo.ast.SymbolicAtom(new_term)
            #add rules of the form fail :-l+, not l-. and fail :-l-, not l+.  
            if self.parsing_first_program:
                try:
                    #add fail :- a_p not a_n for every rule in P2
                    f_1 = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_P + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_P, node.head.atom.symbol.arguments, False)

                    self.suffix_n_literals[self.ANNOTATION_OPEN_N + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_N] = node.head.atom.symbol.name #self.suffix_n
                    f_2 = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_N + node.head.atom.symbol.name + self.ANNOTATION_CLOSE_N, node.head.atom.symbol.arguments, False)
                    l_1 = clingo.ast.Literal(node.location, False, f_1)
                    l_2 = clingo.ast.Literal(node.location, True, f_2)
                    self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
                    fail_head = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
                    fail_body = [l_1, l_2]
                    self.placeholder_program = self.placeholder_program + str(clingo.ast.Rule(node.location, fail_head, fail_body)) + "\n"
                    nl_1 = clingo.ast.Literal(node.location, True, f_1)
                    nl_2 = clingo.ast.Literal(node.location, False, f_2)
                    fail_body = [nl_1, nl_2]
                    self.placeholder_program = self.placeholder_program + str(clingo.ast.Rule(node.location, fail_head, fail_body)) + "\n"
                except:
                    print("Usupported head")
                    exit(1)
        else: 
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            new_head = clingo.ast.SymbolicAtom(new_term)

        self.placeholder_program = self.placeholder_program + str(clingo.ast.Rule(node.location, new_head, rewritten_body)) + "\n"
    


    def compute_placeholder_program(self):
        self.constraint_program_rewriter.compute_placeholder_program()
        #do not parse also constraint program - it will be treated separately
        for i in range(len(self.original_programs_list)-1):
            program = self.original_programs_list[i]
            #for first program the rewriter must do the reduct while for the others it should do just the or
            #and rewrite all the predicates from the first program over the + signature
            self.parsing_first_program = True if i == 0 else False
            self.placeholder_program = ""
            parse_string(program.rules, lambda stm: (self(stm)))
            if not self.ground_transformation:
                self.placeholder_programs_list_rules.append(self.placeholder_program)
            else:
                self.placeholder_programs_list_rules.append(self.placeholder_program.split("\n"))
            self.placeholder_program = ""

        self.pattern_suffix_p = re.compile('|'.join(re.escape(k) for k in self.suffix_p_literals))
        self.pattern_suffix_n = re.compile('|'.join(re.escape(k) for k in self.suffix_n_literals))
        self.pattern_fail = re.compile('|'.join(re.escape(k) for k in self.fail_literals))
        #one rule per list elem
        if self.ground_transformation:
            self.pattern_suffix_n_negated = re.compile('not ' + '|not '.join(re.escape(k) for k in self.suffix_n_literals)) 
        self.placeholder_programs_list_rules.append(self.constraint_program_rewriter.placeholder_program)