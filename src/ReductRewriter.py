import clingo 
from .QuantifiedProgram import QuantifiedProgram, ProgramQuantifier
from clingo.ast import parse_string
import re

#Takes P_2, ..., P_n : C as programs
#flips quantifiers and constraint if the first program is \forall (i.e. the outermost program was a \exists)
#the first two programs collapse into a single ASP program
class ReductRewriter(clingo.ast.Transformer):
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
    suffix_p : str
    suffix_n : str
    fail_atom_name : str
    suffix_p_literals : dict
    suffix_n_literals : dict
    fail_literals : dict
    ground_transformation : bool
    placeholder_program : str
    placeholder_program_rules : list
    parsing_first_program: bool
    to_rewrite_predicates : set
    current_fail_predicate : str

    def __init__(self, original_programs, suffix_p, suffix_n, fail_atom_name, ground_transformation):
        self.original_programs_list = original_programs
        self.placeholder_programs_list_rules = []
        self.placeholder_program_rules = []
        self.rewritten_programs_list_rules = ["" for _ in range(len(self.original_programs_list))]
        self.rewritten_programs_list = []
        self.ground_transformation = ground_transformation
        self.suffix_p = suffix_p
        self.suffix_n = suffix_n
        self.fail_atom_name = fail_atom_name
        self.suffix_p_literals = dict()
        self.suffix_n_literals = dict()
        self.fail_literals = dict()
        self.to_rewrite_predicates = set()
        self.current_fail_predicate = ""
        #refine
        for i in range(len(self.original_programs_list)):
            self.to_rewrite_predicates = self.to_rewrite_predicates | self.original_programs_list[i].head_predicates


        self.parsing_first_program = False
        
    def replace_or_simplify(self, m):
        #matches are of the form not <pred_name>
        pred_name = m.group(0)[5:len(m.group(0))-1]
        if pred_name in self.model_symbols_set:
            self.erase_rule = True
        return ""

    def rewrite(self, counterexample, iteration):
        self.rewritten_programs_list = []
        suffix_p_iteration = f"{self.suffix_p}{iteration}"
        suffix_n_iteration = f"{self.suffix_n}{iteration}"
                
        self.current_fail_predicate = f"{self.fail_atom_name}{iteration}"

        for i in range(len(self.original_programs_list)):
            self.rewritten_programs_list_rules[i] = self.placeholder_programs_list_rules[i]
            if not self.ground_transformation:
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p_iteration, self.rewritten_programs_list_rules[i])
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + suffix_n_iteration, self.rewritten_programs_list_rules[i])
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
                        rule = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + suffix_n_iteration, rule)
                        rule = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p_iteration, rule)
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
                rewritten_preds.add(f"{pred}{suffix_p_iteration}")
            #this could have weaks
            self.rewritten_programs_list.append(QuantifiedProgram(self.rewritten_programs_list_rules[i], [], quantifier, prg_name, rewritten_preds))
           
        #add rewritten constraint program
        prg_name = self.original_programs_list[-1].name
        rewritten_preds = set()
        for pred in self.original_programs_list[-1].head_predicates:
            rewritten_preds.add(f"{pred}{suffix_p_iteration}") 
           
        self.counterexample_facts = " "
        for symbol in counterexample:
            #symbol predicate in P_2
            if symbol.name in self.original_programs_list[0].head_predicates:
                new_symbol = clingo.Function(symbol.name + suffix_n_iteration, symbol.arguments, symbol.positive)
                self.counterexample_facts = self.counterexample_facts + str(new_symbol) + "."

        #add fail atom as an head predicate (it might be needed by rewritings of subsequent ASPQ programs)
        self.rewritten_programs_list[0].head_predicates.add(self.current_fail_predicate)
        #add counterexample facts in the first exists program
        self.rewritten_programs_list[0].rules += self.counterexample_facts

    def visit_Rule(self, node):
        rewritten_body = []
        new_head = None
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
                                        if condition.atom.symbol.name in self.original_programs_list[0].head_predicates:
                                            if condition.sign:
                                                self.suffix_n_literals[self.ANNOTATION_OPEN_N + condition.atom.symbol.name + self.ANNOTATION_CLOSE_N] = condition.atom.symbol.name
                                                new_term = clingo.ast.Function(condition.location, self.ANNOTATION_OPEN_N + condition.atom.symbol.name + self.ANNOTATION_CLOSE_N)
                                            else:
                                                self.suffix_p_literals[self.ANNOTATION_OPEN_P + condition.atom.symbol.name + self.ANNOTATION_CLOSE_P] = condition.atom.symbol.name
                                                new_term = clingo.ast.Function(condition.location, self.ANNOTATION_OPEN_P + condition.atom.symbol.name + self.ANNOTATION_CLOSE_P)
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
                    #predicates of the first program are rewritten over the + and - signature for mimicking the reduct 
                    #predicates of the remaining programs must be written over a new signature (possibly just the + signature)
                    #for making each refinement to have independent chains of ASP programs
                    elif elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom:
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
                    #l_1 = clingo.ast.Literal(node.location, False, f_1)
                    #l_2 = clingo.ast.Literal(node.location, True, f_2)
                    self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
                    fail_head = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
                    #fail_body = [l_1, l_2]
                    #self.placeholder_program = self.placeholder_program + str(clingo.ast.Rule(node.location, fail_head, fail_body)) + "\n"
                    nl_1 = clingo.ast.Literal(node.location, True, f_1)
                    nl_2 = clingo.ast.Literal(node.location, False, f_2)
                    fail_body = [nl_1, nl_2]
                    self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, fail_head, fail_body)))
                except:
                    print("Usupported head")
                    exit(1)
        else: 
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
            new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            new_head = clingo.ast.SymbolicAtom(new_term)

        self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head, rewritten_body)))
    


    def compute_placeholder_program(self):
        #do not parse also constraint program - it will be treated separately
        for i in range(len(self.original_programs_list)):
            program = self.original_programs_list[i]
            #for first program the rewriter must do the reduct while for the others it should do just the or
            #and rewrite all the predicates from the first program over the + signature
            self.parsing_first_program = True if i == 0 else False
            self.placeholder_program_rules = []
            parse_string(program.rules, lambda stm: (self(stm)))
            self.placeholder_program = "\n".join(self.placeholder_program_rules)
            self.placeholder_program_rules = []
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