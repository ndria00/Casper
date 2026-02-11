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
import clingo.ast

from .Rewriter import Rewriter


class FlipConstraintRewriter(Rewriter):
    unsat_atom = clingo.ast.SymbolicAtom
    add_constraint : bool

    def __init__(self, unsat_pred_name, add_constraint=True):
        super().__init__(unsat_pred_name=unsat_pred_name)
        self.add_constraint= add_constraint
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
        if self.add_constraint:
            self.program.append(f":-not {self.unsat_pred_name}.")
        return node.update(**self.visit_children(node))
