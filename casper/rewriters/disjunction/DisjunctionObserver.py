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
from typing import List

import clingo

from casper.language import QuantifiedProgram, ProgramQuantifier
from casper.utils import SolverSettings

class DisjunctionObserver(clingo.Observer):

    program : QuantifiedProgram
    p1 : QuantifiedProgram
    p2 : QuantifiedProgram
    c  : QuantifiedProgram

    rule_heads : list 
    id_to_symbol: dict[int, clingo.Symbol]

    def __init__(self, program, ctl):
        self.program = program
        self.rule_bodies = []
        self.rule_heads = []
        self.id_to_symbol = {}
        self.p1 = None
        self.p2 = None
        self.c = None
        self.ctl = ctl

    def rewrite(self):
        self.map_ids_to_symbols()
        self.construct_p1()
        self.construct_p2()
        self.construct_c()

    def rule(self, choice: bool, head: List[int], body: List[int]):
        self.rule_heads.append(head)
        self.rule_bodies.append(body)

    def map_ids_to_symbols(self):
        self.id_to_symbol: dict[int, clingo.Symbol] = {}
        for sym_atom in self.ctl.symbolic_atoms:
            lit = sym_atom.literal          # signed solver literal
            self.id_to_symbol[lit]  = sym_atom.symbol
            self.id_to_symbol[-lit] = sym_atom.symbol  # keep negative key too

    def lit_str(self, lit: int) -> str:
        pos = abs(lit)
        sym = self.id_to_symbol.get(pos) or self.id_to_symbol.get(lit)
        #found aux which has no textual repr
        if sym is None:
            return f"aux_{lit}" if lit > 0 else  f"not aux_{-lit}"
        return f"not {sym}" if lit < 0 else str(sym)
    
    def construct_p1(self):
        self.p1 = None
        p1_rules = []

        for sym_atom in self.ctl.symbolic_atoms:
            p1_rules.append(f"{self.lit_str(sym_atom.literal)}:-not {SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{self.lit_str(sym_atom.literal)}.")
            p1_rules.append(f"{SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{self.lit_str(sym_atom.literal)}:-not {self.lit_str(sym_atom.literal)}.")
        
        head_predicates = set()
        for pred in self.program.head_predicates:
            head_predicates.add(pred)
            head_predicates.add(f"{SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{pred}")
        self.p1 = QuantifiedProgram("\n".join(p1_rules) + "\n" + self.program.rules_as_constraints, [], ProgramQuantifier.EXISTS, "p_1", head_predicates, False, False)

    def construct_p2(self):
        self.p2 = None
        p2_rules = []
        p2_diff_rules = []

        for sym_atom in self.ctl.symbolic_atoms:
            symbol = sym_atom.symbol
            p2_rules.append(f"{self.clone_sym_str(symbol)}:-not {SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{self.clone_sym_str(symbol)}.")
            p2_rules.append(f"{SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{self.clone_sym_str(symbol)}:-not {self.clone_sym_str(symbol)}.")
    
        #construct subset
        for sym_atom in self.ctl.symbolic_atoms:
            symbol = sym_atom.symbol
            p2_diff_rules.append(f"{SolverSettings.DISJUNCTION_DIFF_ATOM_NAME}:-{self.clone_sym_str(symbol)},{self.lit_str(-sym_atom.literal)}.")
            p2_diff_rules.append(f"{SolverSettings.DISJUNCTION_SUBSET_PRED_NAME}:-not {SolverSettings.DISJUNCTION_DIFF_ATOM_NAME},{self.lit_str(sym_atom.literal)},not {self.clone_sym_str(symbol)}.")
        
        head_predicates = set()
        head_predicates.add(SolverSettings.DISJUNCTION_DIFF_ATOM_NAME)
        head_predicates.add(SolverSettings.DISJUNCTION_SUBSET_PRED_NAME)

        for pred in self.program.head_predicates:
            head_predicates.add(f"{pred}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}")
            head_predicates.add(f"{SolverSettings.DISJUNCTION_FRESH_ATOMS_PREFIX}{pred}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}") 
        self.p2 = QuantifiedProgram("\n".join(p2_rules) + "\n" + self.program.rules_as_constraints_clone + "\n" + "\n".join(p2_diff_rules), [], ProgramQuantifier.FORALL, "p_2", head_predicates, False, False)
    
    def construct_c(self):
        self.c = None
        self.c = QuantifiedProgram(f":- not {SolverSettings.DISJUNCTION_DIFF_ATOM_NAME}, {SolverSettings.DISJUNCTION_SUBSET_PRED_NAME}.\n", [], ProgramQuantifier.CONSTRAINTS, "c", set(), False, False)

    def print_aspq_program(self):
        print(self.p1)
        print(self.p2)
        print(self.c)
    
    def aspq_program(self):
        return [self.p1, self.p2, self.c]

    def clone_sym_str(self, symbol):
        name = symbol.name
        args = symbol.arguments

        clone_atom_name = f"{name}{SolverSettings.DISJUNCTION_CLONE_ATOM_SUFFIX}"

        if args:
            args_str = ",".join(str(a) for a in args)
            return f"{clone_atom_name}({args_str})"
        else:
            return clone_atom_name