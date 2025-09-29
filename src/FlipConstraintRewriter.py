import clingo
import clingo.ast

from .Rewriter import Rewriter


class FlipConstraintRewriter(Rewriter):
    unsat_atom = clingo.ast.SymbolicAtom
    
    def __init__(self, unsat_pred_name):
        super().__init__(unsat_pred_name=unsat_pred_name)
        self.location = clingo.ast.Location(clingo.ast.Position("<generated>", 1, 1), clingo.ast.Position("<generated>", 1, 1))
        self.unsat_atom = clingo.ast.SymbolicAtom(clingo.ast.Function(self.location, self.unsat_pred_name, [], False))
        self.head_predicates.add(unsat_pred_name)
        
    def visit_Rule(self, node):
        head  = node.head
        if head.ast_type == clingo.ast.ASTType.Literal:
            if not head.atom.ast_type == clingo.ast.ASTType.BooleanConstant:
                self.extract_predicate_from_literal(head)         
            else:
                #head of constraints end up here
                self.program.append(str(clingo.ast.Rule(node.location, self.unsat_atom, node.body)))
                return node.update(**self.visit_children(node))
        elif clingo.ast.ASTType.Aggregate:
            self.extract_predicate_from_choice(head)

        self.program.append(str(node))
        return node.update(**self.visit_children(node))
    
    def visit_Program(self, node):
        self.program.append(f":-not {self.unsat_pred_name}.")
        return node.update(**self.visit_children(node))
