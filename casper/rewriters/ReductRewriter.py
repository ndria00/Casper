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
import clingo 
from casper.language import QuantifiedProgram, ProgramQuantifier
from casper.utils.SolverSettings import SolverSettings
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

    original_programs_list : list[QuantifiedProgram]
    placeholder_programs_list_rules : list
    rewritten_programs_list : list
    rewritten_programs_list_rules : list
    suffix_p : str
    suffix_n : str
    fail_atom_name : str
    suffix_p_literals : dict
    suffix_n_literals : dict
    fail_literals : dict
    pure_choice : bool
    placeholder_program : str
    placeholder_program_rules : list
    parsing_first_program: bool
    to_rewrite_predicates : set
    current_fail_predicate : str
    aggregate_reduct: bool

    def __init__(self, original_programs, suffix_p, suffix_n, fail_atom_name, pure_choice):
        self.original_programs_list = original_programs
        self.placeholder_programs_list_rules = []
        self.placeholder_program_rules = []
        self.rewritten_programs_list_rules = ["" for _ in range(len(self.original_programs_list))]
        self.rewritten_programs_list = []
        self.pure_choice = pure_choice
        self.suffix_p = suffix_p
        self.suffix_n = suffix_n
        self.fail_atom_name = fail_atom_name
        self.suffix_p_literals = dict()
        self.suffix_n_literals = dict()
        self.fail_literals = dict()
        self.to_rewrite_predicates = set()
        self.current_fail_predicate = ""
        self.aggregate_reduct = False
        #refine
        for i in range(len(self.original_programs_list)):
            if self.original_programs_list[i].contains_aggregates:
                self.aggregate_reduct = True
            self.to_rewrite_predicates = self.to_rewrite_predicates | self.original_programs_list[i].head_predicates

        self.parsing_first_program = False
        

    def rewrite(self, counterexample, iteration):
        self.rewritten_programs_list = []
        suffix_p_iteration = f"{self.suffix_p}{iteration}"
        suffix_n_iteration = f"{self.suffix_n}{iteration}"
                
        self.current_fail_predicate = f"{self.fail_atom_name}{iteration}"

        for i in range(len(self.original_programs_list)):

            self.rewritten_programs_list_rules[i] = self.placeholder_programs_list_rules[i]
            if not len(self.suffix_p_literals) == 0:
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_p.sub(lambda a : self.suffix_p_literals[a.group(0)] + suffix_p_iteration, self.rewritten_programs_list_rules[i])
            if not len(self.suffix_n_literals) == 0:
                self.rewritten_programs_list_rules[i] = self.pattern_suffix_n.sub(lambda a : self.suffix_n_literals[a.group(0)] + suffix_n_iteration, self.rewritten_programs_list_rules[i])
            if not len(self.fail_literals) == 0:
                self.rewritten_programs_list_rules[i] = self.pattern_fail.sub(lambda a : self.fail_literals[a.group(0)] + str(iteration), self.rewritten_programs_list_rules[i])

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
            self.rewritten_programs_list.append(QuantifiedProgram(self.rewritten_programs_list_rules[i], [], quantifier, prg_name, rewritten_preds, self.original_programs_list[i].contains_choice, self.original_programs_list[i].contains_disjunction))
           
        #add rewritten constraint program
        prg_name = self.original_programs_list[-1].name
        rewritten_preds = set()
        for pred in self.original_programs_list[-1].head_predicates:
            rewritten_preds.add(f"{pred}{suffix_p_iteration}") 
           
        self.counterexample_facts = " "
        counterexample_facts_signature = suffix_n_iteration if not self.pure_choice else suffix_p_iteration
        for symbol in counterexample:
            #symbol predicate in P_2
            if symbol.name in self.original_programs_list[0].head_predicates:
                new_symbol = clingo.Function(symbol.name + counterexample_facts_signature, symbol.arguments, symbol.positive)
                self.counterexample_facts = self.counterexample_facts + str(new_symbol) + ". "

        #add fail atom as an head predicate (it might be needed by rewritings of subsequent ASPQ programs)
        self.rewritten_programs_list[0].head_predicates.add(self.current_fail_predicate)
        #add counterexample facts in the first exists program
        self.rewritten_programs_list[0].rules += self.counterexample_facts
    
    #used for programs for which the reduct must not be simulated - remap the aggregate to positive signature
    def rewrite_choice_head_aggregate_to_positive_signature(self, node):
        new_elements = []
        for elem in node.head.elements:
            new_term = self.create_substitution(node.location, elem.literal.atom.symbol.name, elem.literal.atom.symbol.arguments, True)
            new_head_pos = clingo.ast.SymbolicAtom(new_term)

            new_body = []
            for cond in elem.condition:
                if not cond.atom.ast_type == clingo.ast.ASTType.Comparison:
                    symb_atom = cond.atom.symbol
                    if symb_atom.name in self.original_programs_list[0].head_predicates:
                        new_term = self.create_substitution(node.location, symb_atom.name, symb_atom.arguments, True)
                        new_atom = clingo.ast.SymbolicAtom(new_term)
                        new_literal = clingo.ast.Literal(cond.location, cond.sign, new_atom)
                        new_body.append(new_literal)
                else:
                    new_body.append(cond)
            new_element = clingo.ast.ConditionalLiteral(node.location, new_head_pos, new_body)
            new_elements.append(new_element)
        return clingo.ast.Aggregate(node.location, None, new_elements, None)

    def create_fail_rules(self, pred_name, terms, loc):
        #add rules of the form fail :-l+, not l-. and fail :-l-, not l+.  
        if self.parsing_first_program:

            remapped_terms = []
            for i in range(len(terms)):
                remapped_terms.append(clingo.ast.Variable(loc, f"{SolverSettings.DUMMY_VARIABLE_NAME_IN_FAIL_RULES_PREFIX}{i}"))

            t_pos = self.create_substitution(loc, pred_name, remapped_terms, True)
            t_neg = self.create_substitution(loc, pred_name, remapped_terms, False)
            #add fail :- a_p not a_n for every rule in P2

            l_1 = clingo.ast.Literal(loc, False, t_pos)
            l_2 = clingo.ast.Literal(loc, True, t_neg)

            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
            fail_head = clingo.ast.Function(loc, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            fail_body = [l_1, l_2]
            self.placeholder_program_rules.append(str(clingo.ast.Rule(loc, fail_head, fail_body)))
            
            nl_1 = clingo.ast.Literal(loc, True, t_pos)
            nl_2 = clingo.ast.Literal(loc, False, t_neg)
            fail_body = [nl_1, nl_2]
            self.placeholder_program_rules.append(str(clingo.ast.Rule(loc, fail_head, fail_body)))

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
                                        if not condition.atom.ast_type == clingo.ast.ASTType.Comparison and condition.atom.symbol.name in self.original_programs_list[0].head_predicates:
                                            self.create_substitution_and_add(node.location, condition.atom.symbol.name, condition.atom.symbol.arguments, condition.sign, new_condition)
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
                                new_term = self.create_substitution(node.location, elem.atom.symbol.name, elem.atom.symbol.arguments, True)
                                new_atom = clingo.ast.SymbolicAtom(new_term)
                                new_literal = clingo.ast.Literal(node.location, elem.sign, new_atom)
                                rewritten_body.append(new_literal)
                            else:
                                rewritten_body.append(elem)
                        else:
                            #parsing first program
                            #if predicate is defined in the program for which I am writing the reduct, map it to the + and - signatures
                            #if not doing aggregate reduct it is mapped only to one signature - the one corresponding to its sign
                            if elem.atom.symbol.name in self.original_programs_list[0].head_predicates:
                                self.create_substitution_and_add(node.location, elem.atom.symbol.name, elem.atom.symbol.arguments, elem.sign , rewritten_body)
                            else:#if predicate is not defined in the program for which I am writing the reduct, leave it as it is
                                rewritten_body.append(elem)
                    else:
                        rewritten_body.append(elem)
                else:
                    raise Exception("body atom is None")    
            else:
                rewritten_body.append(elem)
                
        #disable all programs after the program for which I compute the reduct
        if not self.parsing_first_program and not self.pure_choice:
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name #fail
            fail_func = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
            fail_lit = clingo.ast.Literal(node.location, clingo.ast.Sign.Negation, clingo.ast.SymbolicAtom(fail_func))
            rewritten_body.append(fail_lit)

        if node.head.ast_type == clingo.ast.ASTType.Literal and node.head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
            self.fail_literals[self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F] = self.fail_atom_name
            if self.parsing_first_program:
                if not self.pure_choice:
                    new_term = clingo.ast.Function(node.location, self.ANNOTATION_OPEN_F + self.fail_atom_name + self.ANNOTATION_CLOSE_F, [], False)
                    new_head = clingo.ast.SymbolicAtom(new_term)
                    self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head, rewritten_body)))
            else:
                self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, node.head, rewritten_body)))        
        else:
            new_heads = []
            new_bodies = []
            if node.head.ast_type == clingo.ast.ASTType.Aggregate:
                if self.parsing_first_program:
                    for elem in node.head.elements:
                        new_body = rewritten_body.copy()
                        
                        #add head on negative signature in the body in such a way that the rule is simplified if the head is not true on the negative signature (to simulate the reduct of choice rules)
                        new_term_n = self.create_substitution(node.location, elem.literal.atom.symbol.name, elem.literal.atom.symbol.arguments, False)
                        new_term_p = self.create_substitution(node.location, elem.literal.atom.symbol.name, elem.literal.atom.symbol.arguments, True)
                        #add fail rules 
                        self.create_fail_rules(elem.literal.atom.symbol.name, elem.literal.atom.symbol.arguments, node.location)

                        new_heads.append(new_term_p)
                        new_head_neg = clingo.ast.SymbolicAtom(new_term_n)
                        new_body.append(new_head_neg)

                        for cond in elem.condition:
                            if not cond.atom.ast_type == clingo.ast.ASTType.Comparison:
                                symb_atom = cond.atom.symbol
                                if symb_atom.name in self.original_programs_list[0].head_predicates:
                                    self.create_substitution_and_add(node.location, symb_atom.name, symb_atom.arguments, cond.sign , new_body)
                            else:
                                new_body.append(cond)

                        new_bodies.append(new_body)               
                else:
                    #iterate over all choice elements and body and map all literals to the + signature
                    new_heads.append(self.rewrite_choice_head_aggregate_to_positive_signature(node))
                    new_bodies.append(rewritten_body)
            else:
                t_pos = self.create_substitution(node.location, node.head.atom.symbol.name, node.head.atom.symbol.arguments, True)
                if self.parsing_first_program:
                    #add fail rules
                    self.create_fail_rules(node.head.atom.symbol.name, node.head.atom.symbol.arguments, node.location)
                new_heads.append(t_pos)
                new_bodies.append(rewritten_body)
            
            for idx in range(len(new_heads)):
                new_head = new_heads[idx]
                new_body = new_bodies[idx]
        
                if self.parsing_first_program:
                    new_head_l = clingo.ast.Literal(node.location, False, new_head)
                    self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head_l, new_body)))
                else:
                    self.placeholder_program_rules.append(str(clingo.ast.Rule(node.location, new_head, new_body)))
                    

    def compute_placeholder_program(self):
        for i in range(len(self.original_programs_list)):
            program = self.original_programs_list[i]
            #for first program the rewriter must do the reduct while for the others it should do just the or
            #and rewrite all the predicates from the first program over the + signature
            self.parsing_first_program = True if i == 0 else False
            self.placeholder_program_rules = []
            if not self.pure_choice or not self.parsing_first_program: 
                clingo.ast.parse_string(program.rules, lambda stm: (self(stm)))
            self.placeholder_program = "\n".join(self.placeholder_program_rules)
            self.placeholder_program_rules = []

            self.placeholder_programs_list_rules.append(self.placeholder_program)
            self.placeholder_program = ""

        self.pattern_suffix_p = re.compile('|'.join(re.escape(k) for k in self.suffix_p_literals))
        self.pattern_suffix_n = re.compile('|'.join(re.escape(k) for k in self.suffix_n_literals))
        self.pattern_fail = re.compile('|'.join(re.escape(k) for k in self.fail_literals)) 


    def create_substitution(self, location, predicate_name, arguments, positive_signature):
        if positive_signature:
            self.suffix_p_literals[self.ANNOTATION_OPEN_P + predicate_name + self.ANNOTATION_CLOSE_P] = predicate_name
            return clingo.ast.Function(location, self.ANNOTATION_OPEN_P + predicate_name + self.ANNOTATION_CLOSE_P, arguments, False) 
        else:
            self.suffix_n_literals[self.ANNOTATION_OPEN_N + predicate_name + self.ANNOTATION_CLOSE_N] = predicate_name
            return clingo.ast.Function(location, self.ANNOTATION_OPEN_N + predicate_name + self.ANNOTATION_CLOSE_N, arguments, False)
   
    #remap literal to positive and negative signature and add to structure
    def create_substitution_and_add(self, location, pred_name, arguments, sign, structure):
        term = self.create_substitution(location, pred_name, arguments, sign == clingo.ast.Sign.NoSign)
        new_atom = clingo.ast.SymbolicAtom(term)
        new_literal = clingo.ast.Literal(location, sign, new_atom)
        structure.append(new_literal)
        if self.aggregate_reduct:
            term = self.create_substitution(location, pred_name, arguments, not sign == clingo.ast.Sign.NoSign)
            new_atom = clingo.ast.SymbolicAtom(term)
            new_literal = clingo.ast.Literal(location, sign, new_atom)
            structure.append(new_literal)