import clingo
from .QuantifiedProgram import QuantifiedProgram
from clingo.ast import parse_string


class CloneRewriter(clingo.ast.Transformer):
  
    clone_suffix : str
    program : QuantifiedProgram
    rewritten_program_rules : list
    rewritten_program : str
    rewritten_program_head_predicates : set
    found_choice : bool

    def __init__(self, program, clone_suffix):
        self.program = program
        self.clone_suffix = clone_suffix
        self.rewritten_program = ""
        self.rewritten_program_rules = []
        self.rewritten_program_head_predicates = set()
        self.found_choice = False
    
    #clone program is needed just once
    def rewrite(self):
        if self.rewritten_program == "":
            parse_string(self.program.rules, lambda stm: (self(stm)))
            self.rewritten_program = "\n".join(self.rewritten_program_rules) 

    def visit_Rule(self, node):
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
                                    if condition.atom.symbol.name in self.program.head_predicates:
                                        new_term = clingo.ast.Function(condition.location, condition.atom.symbol.name + self.clone_suffix, condition.atom.symbol.arguments, False)
                                        new_atom = clingo.ast.SymbolicAtom(new_term)
                                        new_literal = clingo.ast.Literal(condition.location, condition.sign, new_atom)    
                                        new_condition.append(new_literal)
                                    else:
                                        new_condition.append(condition)    
                                else:
                                    new_condition.append(condition)
                            new_element = clingo.ast.BodyAggregateElement(el.terms, new_condition)
                            new_elements.append(new_element)
                        
                        new_agg = clingo.ast.BodyAggregate(agg.location, agg.left_guard, agg.function, new_elements, agg.right_guard)
                        rewritten_body.append(new_agg)
                    else:
                        if elem.atom.ast_type == clingo.ast.ASTType.SymbolicAtom:
                            if elem.atom.symbol.name in self.program.head_predicates:
                                new_term = clingo.ast.Function(node.location, elem.atom.symbol.name + self.clone_suffix, elem.atom.symbol.arguments, False)
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
        new_head = node.head

        if node.head.ast_type == clingo.ast.ASTType.Aggregate:
            self.found_choice = True
            choice_elements = []
            for choice_element in node.head.elements:
                assert choice_element.ast_type == clingo.ast.ASTType.ConditionalLiteral
                choice_condition = []
                choice_literal = choice_element.literal
                new_choice_term = clingo.ast.Function(choice_literal.location, choice_literal.atom.symbol.name + self.clone_suffix, choice_literal.atom.symbol.arguments, False)
                new_choice_atom = clingo.ast.SymbolicAtom(new_choice_term)
                new_chocie_literal = clingo.ast.Literal(choice_literal.location, choice_literal.sign, new_choice_atom)

                for literal in choice_element.condition:
                    if literal.atom.ast_type == clingo.ast.ASTType.SymbolicAtom:
                        if literal.atom.symbol.name in self.program.head_predicates:
                            new_term = clingo.ast.Function(literal.location, literal.atom.symbol.name + self.clone_suffix, literal.atom.symbol.arguments, False)
                            new_atom = clingo.ast.SymbolicAtom(new_term)
                            new_literal = clingo.ast.Literal(literal.location, literal.sign, new_atom)
                            choice_condition.append(new_literal)
                        else:
                            choice_condition.append(literal)    
                    else:
                        choice_condition.append(literal)

                choice_elements.append(clingo.ast.ConditionalLiteral(choice_element.location, new_chocie_literal, choice_condition))
                new_head=clingo.ast.Aggregate(location=node.head.location, left_guard=node.head.left_guard, elements=choice_elements, right_guard=node.head.right_guard)
        else:
            if node.head.atom.ast_type != clingo.ast.ASTType.BooleanConstant:
                if node.head.ast_type == clingo.ast.ASTType.Literal:
                    new_term = clingo.ast.Function(node.location, node.head.atom.symbol.name + self.clone_suffix, node.head.atom.symbol.arguments, False)
                    new_head = clingo.ast.SymbolicAtom(new_term)
                    self.rewritten_program_head_predicates.add(node.head.atom.symbol.name + self.clone_suffix)   
                    
        self.rewritten_program_rules.append(str(clingo.ast.Rule(node.location, new_head, rewritten_body)))