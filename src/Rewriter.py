import clingo
import clingo.ast


class Rewriter(clingo.ast.Transformer):
    unsat_pred_name : str
    program : list[str]
    head_predicates : set
    propositional_program : bool

    def __init__(self, unsat_pred_name=None):
        super().__init__()
        self.unsat_pred_name = unsat_pred_name
        self.program = []
        self.head_predicates = set()
        self.propositional_program = True

    def visit_Literal(self, node):
        return node.update(**self.visit_children(node))

    def visit_Rule(self, node):
        pass
    
    def visit_Program(self, node):
        pass

    def visit_Variable(self, node):
        self.propositional_program = False
        return node.update(**self.visit_children(node))
    
    def visit_SymbolicTerm(self, node):
        self.propositional_program = False
        return node.update(**self.visit_children(node))
    
    def extract_predicate_from_literal(self, node):
        #print(f"Added {node.atom.symbol.name} to head predicates")
        self.head_predicates.add(node.atom.symbol.name) 
       
    def extract_predicate_from_choice(self, node):
        for elem in node.elements:
            self.head_predicates.add(elem.literal.atom.symbol.name)
            #print(f"Added {elem.literal.atom.symbol.name} to head predicates")

    def reset(self):
        self.program = []
        self.head_predicates = set()
