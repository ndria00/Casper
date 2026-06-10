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


class WFPropagator(clingo.Propagator):
    def __init__(self):
        self.true_atoms  = set()
        self.false_atoms = set()

    def init(self, init: clingo.PropagateInit):
        assignment = init.assignment
        for atom in init.symbolic_atoms:
            solver_lit = init.solver_literal(atom.literal)
            val = assignment.value(solver_lit)
            sym = atom.symbol
            if val is True:
                self.true_atoms.add(sym)
            elif val is False:
                self.false_atoms.add(sym)