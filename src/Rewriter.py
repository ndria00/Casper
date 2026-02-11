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

    def visit_Minimize(self, node):
        pass
        
    def reset(self):
        self.program = []
        self.head_predicates = set()
