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
from typing import List

from casper.language import QuantifiedProgram, ProgramQuantifier
from casper.loggers import ClingoLogger
from .DisjunctionObserver import DisjunctionObserver

class DisjunctionRewriter:
    
    programs : List[QuantifiedProgram]
    rewritten_programs : List[QuantifiedProgram]
    observer : DisjunctionObserver

    def __init__(self, programs):
        self.programs = programs
        self.rewritten_programs = []
        
        if self.programs[0].program_type != ProgramQuantifier.EXISTS:
            raise Exception("Disjunctive program must be existential")
        
        if len(self.programs) > 1 and self.programs[1].rules != "":
            raise Exception("Constraint for disjunctive program must be empty")
        
        self.logger = ClingoLogger()
        self.ctl = clingo.Control(logger=self.logger)        
        self.ctl.add(self.programs[0].rules)
        self.observer = DisjunctionObserver(self.programs[0], self.ctl)
        self.ctl.register_observer(self.observer)

    def rewrite(self):
        self.ctl.ground()
        self.observer.rewrite()
        return self.observer.aspq_program()
