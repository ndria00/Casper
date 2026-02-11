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

from .SolverSettings import SolverSettings
from .Rewriter import Rewriter


class RelaxedRewriter(Rewriter):
    weak_level : int
    def __init__(self, weak_level, unsat_pred_name):
        super().__init__(unsat_pred_name=unsat_pred_name)
        self.weak_level=weak_level
        
    def visit_Rule(self, node):
        head  = node.head
        if head.ast_type == clingo.ast.ASTType.Literal:
            try:
                self.extract_predicate_from_literal(head)         
            except:
                pass #head of constraints end up here
        elif clingo.ast.ASTType.Aggregate:
            self.extract_predicate_from_choice(head)

        unsat_atom = clingo.ast.SymbolicAtom(clingo.ast.Function(node.location, self.unsat_pred_name, [], False))

        node.body.insert(0, clingo.ast.Literal(location = node.location, sign=clingo.ast.Sign.Negation, atom=unsat_atom))
        self.program.append(str(clingo.ast.Rule(node.location, node.head, node.body)))
        return node.update(**self.visit_children(node))

    def visit_Program(self, node):
        choice = "{" + f"{self.unsat_pred_name}" + "}."
        weak = f":~{self.unsat_pred_name}. [{SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS}@{self.weak_level}]"
        self.program.append(weak)
        self.program.append(choice)
        return node.update(**self.visit_children(node))
