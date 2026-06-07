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
from pathlib import Path
import clingo
from clingo.ast import parse_string

from casper.output import ASPChefModelPrinter
from casper.loggers import ClingoLogger
from casper.rewriters import CostRewriter, RefinementBlockingClauseRewriter
from casper.rewriters import RefinementGlobalWeakRewriter
from casper.rewriters import WeakObserver
from casper.rewriters import RefinementWeakRewriter
from casper.rewriters import RelaxedRewriter
from casper.rewriters import CounterexampleRewriter
from casper.rewriters import RefinementRewriter
from casper.rewriters import RefinementNoWeakRewriter
from casper.utils import SolverStatistics
from casper.utils import SolverSettings
from casper.output import ConstraintModelPrinter
from casper.output import ModelPrinter
from casper.loggers import MyLogger
from casper.output import PositiveModelPrinter
from .ProgramsHandler import ProgramsHandler

import time

class ASPQSolver:
    programs_handler : ProgramsHandler
    ctl_move : clingo.Control
    ctl_move_has_weak : bool
    ctl_move_weak_observer : WeakObserver
    ctl_countermove : clingo.Control
    ctl_countermove_has_weak : bool
    ctl_countermove_weak_observer : WeakObserver
    assumptions : list
    symbols_defined_in_first_program : dict
    output_symbols_defined_in_first_program : dict

    current_candidate : clingo.solving._SymbolSequence
    current_candidate_symbols_set : set
    current_counterexample : clingo.solving._SymbolSequence
    current_candidate_cost : list
    current_counterexample_cost : list
    current_counterexample_symbols_set : set
    last_quantified_model : clingo.solving._SymbolSequence
    last_quantified_model_cost : list
    
    refinement_global_weak_rewriter : RefinementGlobalWeakRewriter
    refinement_rewriter : RefinementRewriter
    counterexample_rewriter: CounterexampleRewriter
    models_found : int
    exists_first: bool
    model_printer : ModelPrinter
    logger : MyLogger
    settings : SolverSettings
    sub_solvers_settings : SolverSettings
    program_levels : int
    main_solver : bool
    depth : int
    output_pad :str
    p1_predicates_are_output : bool
    counterexample_found : int
    optimum_found : bool
    fail_atoms : list
    dominated_atoms : list
    violated_constraint_atoms : list
    violated_global_weak_atoms : list
    fail_found : bool
    dominated_found : bool
    violated_constraint_found : bool
    violated_global_bound_found : bool
    unsat_c_predicate_found : bool
    clingo_logger : ClingoLogger

    def __init__(self, programs_handler, solver_settings, main_solver, depth):
        self.programs_handler = programs_handler
        self.depth = depth
        self.output_pad = self.depth * '\t'
        self.settings = solver_settings
        #sub solvers are always required to compute one model, inherit the same debug flag as the parent,
        #never print the model as a constraint since no enumeration is needed, apply ground transformations iff the current solver does
        self.sub_solvers_settings = SolverSettings(1, self.settings.debug, False, self.settings.pure_choice, self.settings.no_weak, self.settings.collapse_global_weak, self.settings.json_format, self.settings.blocking_ref)
        self.program_levels = len(self.programs_handler.programs_list) -1
        self.assumptions = []
        self.counterexample_rewriter = None
        self.refinement_rewriter = None
        
        if self.settings.constraint_print:
            self.model_printer = ConstraintModelPrinter()
        elif self.settings.json_format:
            self.model_printer = ASPChefModelPrinter()
        else:
            self.model_printer = PositiveModelPrinter()

        self.exists_first = self.programs_handler.exists_first()
        self.main_solver = main_solver
        self.refinement_global_weak_rewriter = None
        if not self.programs_handler.global_weak_program is None:
            self.refinement_global_weak_rewriter = RefinementGlobalWeakRewriter(self.programs_handler.global_weak_program)
        if self.program_levels > 2:
            #define counterexample and refinement solvers
            self.counterexample_solver = None
            self.refinement_solver =  None

        self.p1_predicates_are_output = len(self.programs_handler.p(0).output_predicates) == 0
        self.clingo_logger = ClingoLogger()
        self.reset_solver()

    def reset_solver(self):
        self.choice_str = ""
        self.models_found = 0
        self.current_candidate = None
        self.current_counterexample = None
        self.current_candidate_cost = []
        self.current_counterexample_cost = []
        self.current_candidate_symbols_set = set()
        self.current_counterexample_symbols_set = set()

        self.symbols_defined_in_first_program = dict()
        self.output_symbols_defined_in_first_program = dict()
        self.last_quantified_model_cost = None
        self.last_quantified_model = None
        self.counterexample_found = 0
        self.optimum_found = False
        self.fail_atoms = []
        self.dominated_atoms = []
        self.violated_constraint_atoms = []
        self.violated_global_weak_atoms = []
        self.ctl_move_has_weak = False
        self.fail_found = False
        self.dominated_found = False
        self.violated_constraint_found = False
        self.violated_global_bound_found = False
        self.ctl_countermove_has_weak = False
        self.unsat_c_predicate_found = False

    def ground_and_construct_choice_interfaces(self):
        choice = []
        self.ctl_move = clingo.Control(logger=self.clingo_logger.log) 
        self.ctl_move.configuration.solve.opt_mode = "optN"
        self.ctl_move.configuration.solve.models = "0"

        #used to search for unsat_c when ASPQ programs have local weak (in counterexample or in candidate for 1-ASPQ)
        self.unsat_c_atom = clingo.Function(SolverSettings.UNSAT_C_PREDICATE, [])

        self.settings.logger.debug("%sAdded First program to ctl move:\n%s", self.output_pad, self.programs_handler.p(0).rules)
        self.ctl_move.add(self.programs_handler.p(0).rules)

        if self.programs_handler.p(0).contains_weak():
            #add weak
            weak_repr = "\n".join(str(weak) for weak in self.programs_handler.p(0).weak_constraints)
            self.settings.logger.debug("%sAdded First program weak constraints to ctl move:\n%s", self.output_pad, weak_repr)
            if len(self.programs_handler.p(0).weak_constraints) > 0:
                self.ctl_move_has_weak = True
            self.ctl_move.add(weak_repr)
            self.ctl_move_weak_observer = WeakObserver()
            self.ctl_move.register_observer(self.ctl_move_weak_observer)

        self.settings.logger.debug("%sAdded choice to ctl move:\n%s", self.output_pad, self.choice_str)
        self.ctl_move.add(self.choice_str)
        if self.programs_handler.instance != "":
            self.settings.logger.debug("%sAdded instance to ctl move:\n%s", self.output_pad, self.programs_handler.instance)
            self.ctl_move.add(self.programs_handler.instance)
        
        #1-ASP(Q) programs always have a constraint program - it is created without rules when a constraint program is not parsed
        if self.program_levels == 1:
            #in case of exists_weak : C and \forall_weak C the program was already rewritten (c is the empty program and the original constraint program was absorbed in P_1)
            if self.programs_handler.last_exists():
                if not self.programs_handler.p(0).contains_weak():
                    self.settings.logger.debug("%sAdded constraint program to ctl move:\n%s", self.output_pad, self.programs_handler.c().rules)
                    self.ctl_move.add(self.programs_handler.c().rules)
            else:
                if not self.programs_handler.p(0).contains_weak():
                    self.settings.logger.debug(f"%sAdded flipped constraint program to ctl move:\n%s", self.output_pad, self.programs_handler.neg_c().rules)
                    self.ctl_move.add(self.programs_handler.neg_c().rules)
            self.ctl_move.ground()
            for atom in self.ctl_move.symbolic_atoms:
                if atom.symbol.name in self.programs_handler.p(0).head_predicates:
                    self.symbols_defined_in_first_program[atom.symbol] = None
                    if not self.p1_predicates_are_output and atom.symbol.name in self.programs_handler.p(0).output_predicates:
                        self.output_symbols_defined_in_first_program[atom.symbol] = None
            
            if self.p1_predicates_are_output:
                self.output_symbols_defined_in_first_program = self.symbols_defined_in_first_program
            self.settings.logger.debug("%sGrounded ctl move", self.output_pad)
            return
        else:
            if self.programs_handler.p(1).contains_weak():
                self.refinement_rewriter = RefinementWeakRewriter([self.programs_handler.p(1)], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.pure_choice)
                self.refinement_rewriter.compute_placeholder_program()
            
            if not self.programs_handler.global_weak_program is None and not self.settings.collapse_global_weak:
                cost_global_constraint_rewriter = CostRewriter(self.programs_handler.global_weak_program, SolverSettings.GLOBAL_WEAK_VIOLATION_ATOM_NAME, "", "", True, False)
                cost_global_constraint_rewriter.rewrite()
                self.ctl_move.add(cost_global_constraint_rewriter.rewritten_program)
                self.settings.logger.debug("%sAdded cost program for global weak to ctl move:\n%s", self.output_pad, cost_global_constraint_rewriter.rewritten_program)
            
            self.ctl_move.ground()
            choice = []
            disjoint = True
            for atom in self.ctl_move.symbolic_atoms:
                if atom.symbol.name in self.programs_handler.p(0).head_predicates:
                    self.symbols_defined_in_first_program[atom.symbol] = None
                    if not self.p1_predicates_are_output and atom.symbol.name in self.programs_handler.p(0).output_predicates:
                        self.output_symbols_defined_in_first_program[atom.symbol] = None
                    choice.append(str(atom.symbol))
                    disjoint = False
    
            #compute total cost for level and construct template aggregate constraint
            if not self.programs_handler.global_weak_program is None:
                self.refinement_global_weak_rewriter.compute_placeholder_program(self.ctl_move.symbolic_atoms)

            if self.p1_predicates_are_output:
                self.output_symbols_defined_in_first_program = self.symbols_defined_in_first_program
            #add choice in the next program
            if not disjoint:
                if len(choice) > 0:
                    sub_choice_str = ";".join(choice) 
                    sub_choice_str = "{"+ sub_choice_str + "}. "
                    self.choice_str += sub_choice_str
                    self.settings.logger.debug("%sConstructed choice:\n%s", self.output_pad, self.choice_str)

            
            #ground the second program with its cost rewriting and with the choice from the first program    
            #add level facts inside first program
            if self.programs_handler.p(1).contains_weak():
                ctl_weak = clingo.Control(logger=self.clingo_logger.log)
                cost_p2_rewriter = CostRewriter(self.programs_handler.p(1),SolverSettings.WEAK_VIOLATION_ATOM_NAME, SolverSettings.LEVEL_COST_ATOM_NAME, SolverSettings.COST_AT_LEVEL_ATOM_NAME, True, False)
                cost_p2_rewriter.rewrite()
                ctl_weak.add(self.choice_str + self.programs_handler.p(1).rules + cost_p2_rewriter.rewritten_program_with_aggregate())
                ctl_weak.ground()
                level_facts = []
                for atom in ctl_weak.symbolic_atoms:
                    if atom.symbol.name == SolverSettings.WEAK_VIOLATION_ATOM_NAME:
                        level_facts.append(f"{SolverSettings.LEVEL_COST_ATOM_NAME}({atom.symbol.arguments[1]}).")
                level_facts_str = "\n".join(level_facts)
                self.settings.logger.debug("%sAdded weak levels to ctl move %s", self.output_pad, level_facts_str)
                self.ctl_move.add("levels", [], level_facts_str)
                self.ctl_move.ground([("levels", [])])
                

            if self.program_levels == 2:
                self.ctl_countermove = clingo.Control(logger=self.clingo_logger.log)
                self.ctl_countermove.configuration.solve.opt_mode = "optN"
                self.ctl_countermove.configuration.solve.models = "0"
                self.settings.logger.debug("%sadded choice to ctl countermove:\n%s", self.output_pad, self.choice_str)
                self.ctl_countermove.add(self.choice_str)
                self.ctl_countermove.add(self.programs_handler.p(1).rules)
                self.settings.logger.debug("%sadded second program to ctl countermove:\n%s", self.output_pad, self.programs_handler.p(1).rules)
                if not self.programs_handler.p(1).contains_weak():
                    if self.programs_handler.last_exists():
                        self.ctl_countermove.add(self.programs_handler.c().rules)
                        self.settings.logger.debug("%sadded constraint to ctl countermove:\n%s", self.output_pad, self.programs_handler.c().rules)
                    else:
                        self.settings.logger.debug("%sadded flipped constraint to ctl countermove:\n%s", self.output_pad, self.programs_handler.neg_c().rules)
                        self.ctl_countermove.add(self.programs_handler.neg_c().rules)
                #second program contains weak which were not rewritten
                else:
                    weak_repr = "\n".join(str(weak) for weak in self.programs_handler.p(1).weak_constraints)
                    self.ctl_countermove.add(weak_repr)
                    self.ctl_countermove_has_weak = True
                    self.settings.logger.debug("%sadded weak to ctl countermove:\n%s", self.output_pad, weak_repr)
                    self.relaxed_rewriter = RelaxedRewriter(SolverSettings.WEAK_NO_MODEL_LEVEL, SolverSettings.UNSAT_C_PREDICATE)

                    if self.programs_handler.exists_first():
                        parse_string(self.programs_handler.neg_c().rules, lambda stm: (self.relaxed_rewriter(stm)))
                    else:
                        parse_string(self.programs_handler.c().rules, lambda stm: (self.relaxed_rewriter(stm)))
                    relaxed_constraint = "\n".join(self.relaxed_rewriter.program)
                    self.settings.logger.debug("%sadded relaxed constraint to ctl countermove:\n%s", self.output_pad, relaxed_constraint)
                    self.ctl_countermove.add(relaxed_constraint)
                    self.ctl_countermove_weak_observer = WeakObserver()
                    self.ctl_countermove.register_observer(self.ctl_countermove_weak_observer)

                self.ctl_countermove.ground()

    def on_candidate(self, model):
        self.current_candidate_cost = model.cost
        self.current_candidate = model.symbols(shown=True)
        if not self.programs_handler.global_weak_program is None:
            self.violated_global_bound_found = any(model.contains(atom) for atom in self.violated_global_weak_atoms)
        if self.ctl_move_has_weak:    
            #check if all fail dominated and violated_constraint are in model
            if model.optimality_proven:
                if self.program_levels == 1:
                    self.unsat_c_predicate_found = model.contains(self.unsat_c_atom)
                self.fail_found = all(model.contains(fail_atom) for fail_atom in self.fail_atoms)
                self.dominated_found = all(model.contains(dominated_atom) for dominated_atom in self.dominated_atoms)
                self.violated_constraint_found = any(model.contains(violated_constraint_atom) for violated_constraint_atom in self.violated_constraint_atoms)
            return not model.optimality_proven
        return False
        
    def on_counterexample(self, model):
        self.current_counterexample_cost = model.cost
        self.current_counterexample = model.symbols(shown=True)
        if self.ctl_countermove_has_weak:           
            if model.optimality_proven:
                self.unsat_c_predicate_found = model.contains(self.unsat_c_atom)
            return not model.optimality_proven 
        return False

    def finished_search_for_candidate(self, result):
        if not result.unsatisfiable:
            self.current_candidate_symbols_set.clear()
            for symbol in self.current_candidate:
                self.current_candidate_symbols_set.add(symbol)

    def finished_search_for_counterexample(self, result):
        if not result.unsatisfiable:
            self.current_counterexample_symbols_set.clear()
            for symbol in self.current_counterexample:
                self.current_counterexample_symbols_set.add(symbol)


    #add quantified answer set as constraint for enabling enumeration        
    def add_model_as_constraint(self):
        constraint = ":-"
        for symbol in self.output_symbols_defined_in_first_program.keys():
            if symbol in self.current_candidate_symbols_set:
                constraint += f"{symbol},"
            else:
                constraint += f"not {symbol},"

        constraint = constraint[:-1]
        constraint += "."
        self.settings.logger.debug("%sAdding model as constraint to ctl move:\n%s", self.output_pad, constraint)
        #first program is expanded with constraint
        self.programs_handler.programs_list[0].rules += f"\n{constraint}"
        #if refinement solver was not created (i.e., no CE found so far), add the constraint directly over the ctl_move
        if self.program_levels < 4 or self.refinement_solver is None:
            self.programs_handler.programs_list[0]
            self.ctl_move.add(f"constraint_{self.models_found}", [], constraint)
            self.ctl_move.ground([(f"constraint_{self.models_found}", [])])
        else: #if more than 4 levels and not refinement is None, create a new ASP(Q) solver in which the first program is extended with the constraint
            new_programs_list = [p for p in self.programs_handler.programs_list]
            new_programs_list[0].rules += f"\n{constraint}\n"
            ref_programs_handler = ProgramsHandler(new_programs_list, self.programs_handler.instance, None)
            self.refinement_solver = ASPQSolver(ref_programs_handler, self.sub_solvers_settings, False, self.depth+1)

    def print_projected_model(self, model):
        if self.settings.collapse_global_weak:
            print(self.current_candidate_cost)
        self.model_printer.print_model(model, self.output_symbols_defined_in_first_program)
        if self.settings.collapse_global_weak:
            print("OPTIMUM FOUND")

    #solve function for ASPQ with n levels
    def solve_n_levels(self, external_assumptions, choice_str):
        SolverStatistics().iteration_done()
        self.choice_str = choice_str
        self.external_assumptions = external_assumptions

        self.ground_and_construct_choice_interfaces()

        while self.models_found < self.settings.n_models or self.settings.enumeration:
            satisfiable = self.recursive_cegar()
            if satisfiable:
                if self.exists_first:
                    if not self.programs_handler.global_weak_program is None:
                        current_upper_bound, cost_print = self.refinement_global_weak_rewriter.compute_cost_and_new_upper_bound(self.current_candidate_symbols_set)
                        self.violated_global_weak_atoms.append(clingo.Function(self.refinement_global_weak_rewriter.current_violated_bound_atom_name , []))
                        self.ctl_move_has_weak = True
                        self.settings.logger.debug("%sCurrent upper bound: %s", self.output_pad, current_upper_bound)
                        #last model is optimum
                        #TODO put the cost equal to 2 when enumeration is enabled
                        if self.violated_global_bound_found:
                            if not self.programs_handler.global_weak_program is None:
                                print("OPTIMUM FOUND")
                                self.optimum_found = True
                                self.print_projected_model(self.last_quantified_model)
                            self.models_found += 1
                            return True # enumeration of optimal models not supported yet
                        else:
                            print(f"OPTIMIZATION: {cost_print}")
                            #add constraint with new bound                                    
                            self.settings.logger.debug("%sAdding cost constraint to ctl move %s", self.output_pad, current_upper_bound)
                            self.ctl_move.add(f"optimization_{self.refinement_global_weak_rewriter.iteration}", [], current_upper_bound)
                            self.ctl_move.ground([(f"optimization_{self.refinement_global_weak_rewriter.iteration}", [])])
                    else:
                        self.models_found += 1
                    if self.main_solver:
                        self.print_projected_model(self.current_candidate)
                        SolverStatistics().model_found()
                        self.last_quantified_model_cost = self.current_candidate_cost
                        self.last_quantified_model = self.current_candidate
                        self.current_candidate_cost = []
                        
                    if self.models_found == self.settings.n_models:
                        return True
                    #this is to handle the case in which no symbol is defined in a given program and all false is a quantified answer set
                    if len(self.output_symbols_defined_in_first_program.keys()) == 0:
                        return True
                    self.add_model_as_constraint()
                else:
                    if self.main_solver:
                        SolverStatistics().model_found()
                    return True 
                 
            else:
                #program starts with forall and is unsat
                if not self.exists_first:
                    return False
                                
                if self.exists_first and  not self.programs_handler.global_weak_program is None and not self.last_quantified_model is None:
                    print("OPTIMUM FOUND")
                    self.optimum_found = True
                    self.print_projected_model(self.last_quantified_model)
                    return True
                #program starts with exists and therefore there might be models already found
                #the exit code should depend also on these
                if self.models_found > 0:
                    return True
                else:
                    return False

    def recursive_cegar(self):
        if self.program_levels == 1:
            # Program is \exists P_1:C or \forall P_1:C (with C possibly empty)
            result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_candidate, on_finish=self.finished_search_for_candidate)
            if result.unsatisfiable:
                #exists looses if P_1 \cup C unsat
                #forall wins if P_1 \cup \neg C unsat
                return False if self.programs_handler.last_exists() else True
            if self.programs_handler.p(0).contains_weak():
                #for 1-ASPQW, global weak constraints are added inside P_1 and unsat_c is always added at level -1
                if not self.unsat_c_predicate_found:
                    return True
                else:#unsat_c found 
                    return False
            #exists wins if P_1 \cup C sat
            #forall looses if P_1 \cup \neg C sat            
            return True if self.programs_handler.last_exists() else False
        #\exists P_1 \forall P_2 : C or
        #\forall P_1 \exists P_2 : C
        elif self.program_levels == 2:
            self.settings.logger.debug("%sInside cegar for 2-ASPQ", self.output_pad)
            while True:
                #add model M_1 of P_1 as assumption
                self.assumptions = []
                self.settings.logger.debug("%sSearching for candidate", self.output_pad)
                # Assign external atoms introduced by refinement of programs with weak constraints 
                if self.programs_handler.p(1).contains_weak() and self.counterexample_found > 0:
                    external_preds = self.refinement_rewriter.external_predicates
                    for i in range(len(external_preds) -1):
                        self.ctl_move.assign_external(clingo.Function(external_preds[i]), False)
                    self.ctl_move.assign_external(clingo.Function(external_preds[-1]), True)
                result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_candidate, on_finish=self.finished_search_for_candidate)
                if result.unsatisfiable:
                    self.settings.logger.debug("%sNo candidate found", self.output_pad)
                    #forall wins if P_1 has no sm
                    #exist looses if P_1 has no sm
                    return True if self.programs_handler.forall_first() else False
                else:
                    self.settings.logger.debug("%sCandidate cost: %s", self.output_pad, self.current_candidate_cost)
                    #check if current candidate violates the bound constraint
                    if not self.programs_handler.global_weak_program is None:
                        if self.violated_global_bound_found:
                            return False
                    #Weak refinement introduces weak constraints in the first program
                    #the ASPQ is unsatisfiable when either the move program is unsatisfiable or there is no other 
                    #model left from P_1 that does not admit any countermove - this condition is detected by the
                    #weak constraints at the lowest priority introduced by the refinement
                    if self.programs_handler.p(1).contains_weak():
                        #No new candidate if not fail, not dominated and violated constraint (i.e., there is at least one CE that is again a CE for any possible candidate)
                        if not self.fail_found and not self.dominated_found and self.violated_constraint_found:
                            return True if self.programs_handler.forall_first() else False
                    elif self.programs_handler.p(0).contains_weak():
                        if self.violated_constraint_found:
                            return True if self.programs_handler.forall_first() else False        
                        
                    self.settings.logger.debug("%sFound candidate %s", self.output_pad, self.current_candidate)
                    self.construct_assumptions()
                    #search for counterexample
                    self.settings.logger.debug("%sSearching for counterexample", self.output_pad)
                    result = self.ctl_countermove.solve(assumptions=self.assumptions + self.external_assumptions, on_model=self.on_counterexample, on_finish=self.finished_search_for_counterexample)
                    #winning move for the first quantifier - no recursive call for 2-ASPQ
                    if result.unsatisfiable:
                        self.settings.logger.debug("%sNo counterexample found", self.output_pad)
                        #forall wins if P_2 \cup \neg C has no sm
                        #exists looses if P_2 \cup C has no sm
                        return False if self.programs_handler.last_exists() else True
                    #unsat_c \in model means that ctr(\Pi) is unsatisfiable, which means no counterexample exists
                    #:~unsat_c was added to detect this case when the countermove ctl was created
                    if self.programs_handler.p(1).contains_weak():
                        self.settings.logger.debug("%sCounterexample cost %s", self.output_pad, self.current_counterexample_cost)
                        if self.unsat_c_predicate_found:
                            self.settings.logger.debug("%sNo counterexample found", self.output_pad)
                            return True if self.programs_handler.exists_first() else False
                    self.settings.logger.debug("%sCounterexample found %s", self.output_pad, self.current_counterexample)
                    self.counterexample_found += 1
                    SolverStatistics().counterexample_found()
                    if self.refinement_rewriter is None:
                        if not self.programs_handler.program_contains_weak():
                            if not self.settings.blocking_ref:
                                self.refinement_rewriter = RefinementNoWeakRewriter([self.programs_handler.p(1)], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.pure_choice)
                            else:
                                self.refinement_rewriter = RefinementBlockingClauseRewriter(self.symbols_defined_in_first_program)
                            self.refinement_rewriter.compute_placeholder_program()
                        else:
                            self.refinement_rewriter = RefinementWeakRewriter([self.programs_handler.p(1)], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.pure_choice)
                            self.refinement_rewriter.compute_placeholder_program()

                    
                    if self.settings.blocking_ref and not self.programs_handler.program_contains_weak():
                        self.refinement_rewriter.rewrite(self.current_candidate_symbols_set, SolverStatistics().solvers_iterations)
                    else:
                        self.refinement_rewriter.rewrite(self.current_counterexample, SolverStatistics().solvers_iterations)
                    refinement = self.refinement_rewriter.refined_program()
                    
                    #Add a new external predicate and store new refinement predicates (fail_M, dominated_M, violated_condition_M)
                    if self.programs_handler.p(1).contains_weak():
                        self.ctl_move_has_weak = True
                        refinement += f"#external {self.refinement_rewriter.external_predicates[-1]}.\n"
                        self.fail_atoms.append(clingo.Function(self.refinement_rewriter.current_fail_predicate, []))
                        self.dominated_atoms.append(clingo.Function(self.refinement_rewriter.current_dominated_predicate, []))
                    if self.programs_handler.p(0).contains_weak():
                        self.violated_constraint_atoms.append(clingo.Function(self.refinement_rewriter.current_unsat_c_predicate, []))
                    
                    self.settings.logger.debug("%sResult of refinement:\n%s", self.output_pad, refinement)

                    self.extend_control_and_ground_refinement(refinement)

                    SolverStatistics().iteration_done()
        else:
            self.settings.logger.debug("%sInside recursive cegar for n-ASPQ with n >=3", self.output_pad)
            while True:
                self.assumptions = []
                if self.refinement_solver is None:
                    self.settings.logger.debug("%sSearching for candidate n>=3", self.output_pad)
                    #on the first iteration is just a solve on the outermost program
                    result = self.ctl_move.solve(assumptions = self.external_assumptions, on_model=self.on_candidate, on_finish=self.finished_search_for_candidate)
                    if result.unsatisfiable:
                        self.settings.logger.debug("%sNo candidate found when solving ctl_move", self.output_pad)
                        #no move, current quantifier looses
                        return False if self.exists_first else True
                    else: 
                        self.settings.logger.debug("%sFound candidate %s", self.output_pad, self.current_candidate)
                        self.construct_assumptions()
                else:
                    if self.program_levels > 3:
                        self.settings.logger.debug("%sSearching for candidate - solving ASP(Q) refinement", self.output_pad)
                        self.refinement_solver.reset_solver()
                        satisfiable = self.refinement_solver.solve_n_levels(self.external_assumptions, self.choice_str)
                        SolverStatistics().iteration_done()
                                                
                        if not satisfiable:
                            self.settings.logger.debug("%sNo candidate found when solving refined ASP(Q)", self.output_pad)
                            return False if self.exists_first else True
                        else:
                            self.settings.logger.debug("%sFound candidate by solving refined ASP(Q)%s", self.output_pad, self.refinement_solver.current_candidate)
                            #consider the candidate of the refinement solver as the candidate of this solver (similar to when the model found by solving the ctl_move is set as current candiate)
                            self.current_candidate = self.refinement_solver.current_candidate
                            self.current_candidate_symbols_set = self.refinement_solver.current_candidate_symbols_set
                            self.current_candidate_cost = self.refinement_solver.current_candidate_cost
                    else:
                        result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_candidate, on_finish=self.finished_search_for_candidate)
                        if result.unsatisfiable:
                            return False if self.exists_first else True
                        else:
                            self.settings.logger.debug("%sFound candidate %s", self.output_pad, self.current_candidate)


                if self.counterexample_rewriter is None:
                    self.counterexample_rewriter = CounterexampleRewriter(self.programs_handler.programs_list[1:len(self.programs_handler.programs_list)-1], self.programs_handler.c(), self.programs_handler.neg_c())            
                    self.counterexample_rewriter.rewrite()

                #this is always an ASPQ program with two or more levels
                ce_programs_handler = ProgramsHandler(self.counterexample_rewriter.rewritten_program(), self.programs_handler.instance)
                self.counterexample_solver = ASPQSolver(ce_programs_handler, self.sub_solvers_settings, False, self.depth +1)

                self.construct_assumptions()
                self.counterexample_solver.reset_solver()
                satisfiable = self.counterexample_solver.solve_n_levels(self.external_assumptions + self.assumptions, self.choice_str)
                if satisfiable:
                    self.settings.logger.debug("%sCounterexample found %s", self.output_pad, self.counterexample_solver.current_candidate)
                    SolverStatistics().counterexample_found()
                #no counterexample
                if not satisfiable and self.programs_handler.forall_first():
                    self.settings.logger.debug("%sNo counterexample found", self.output_pad)
                    return False
                    
                if not satisfiable and self.programs_handler.exists_first():
                    self.settings.logger.debug("%sNo counterexample found", self.output_pad)
                    return True
                
                #a counterexample was found
                SolverStatistics().iteration_done()
                if self.refinement_rewriter is None:
                    if not self.settings.blocking_ref:
                        self.refinement_rewriter = RefinementNoWeakRewriter(self.programs_handler.programs_list[1:len(self.programs_handler.programs_list)-1], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.pure_choice)
                    else:
                        self.refinement_rewriter = RefinementBlockingClauseRewriter(self.symbols_defined_in_first_program)
                    self.refinement_rewriter.compute_placeholder_program()
                if not self.settings.blocking_ref:
                    self.refinement_rewriter.rewrite(self.counterexample_solver.current_candidate, SolverStatistics().solvers_iterations)
                else:
                    self.refinement_rewriter.rewrite(self.current_candidate_symbols_set, SolverStatistics().solvers_iterations)
                #program with potentially first quantifiers collapsed and the or applied to remaining quantifiers (and also C)
                refinement = self.refinement_rewriter.refined_program()

                #refinement is an ASP program and can be directly added to the ctl_move
                if type(refinement) == str:
                    self.settings.logger.debug("%sResult of refinement:\n%s", self.output_pad, refinement)
                    self.extend_control_and_ground_refinement(refinement)
                else: #refinement is an ASPQ
                    self.settings.logger.debug("%sResult of refinement is an ASP(Q) - not printed\n", self.output_pad)
                    if self.refinement_solver == None:
                        refinement_handler =  ProgramsHandler(refinement, self.programs_handler.instance)
                        # add rules from P_1 into refinement
                        # this should be done only the first time
                        refinement[0].rules += f"\n{self.programs_handler.p(0).rules}\n"
                        refinement[0].head_predicates = refinement[0].head_predicates | self.programs_handler.p(0).head_predicates
                        self.refinement_solver = ASPQSolver(refinement_handler, self.sub_solvers_settings, False, self.depth +1)
                    else: #when refinement solver is created, the refinement_handler aldready adds refinement... subsequent calls should expand single programs
                        self.extend_control_and_ground_refinement(refinement)
                    
                    
                    assert len(refinement_handler.programs_list) == len(self.refinement_solver.programs_handler.programs_list)
                    
                SolverStatistics().iteration_done()
                
    def extend_control_and_ground_refinement(self, refinement):
        #add first program to ctl_move, call extend on sub-solvers
        if type(refinement) == str:
            self.ctl_move.add(f"iteration_{SolverStatistics().solvers_iterations}", [], refinement)
            self.ctl_move.ground([(f"iteration_{SolverStatistics().solvers_iterations}", [])])
        else:            
            new_programs_list = []
            for i in range(len(refinement)):
                new_programs_list.append(self.refinement_solver.programs_handler.programs_list[i])
                #update each subprogram with rules of or(P_i, \naf as_{m_j})
                new_programs_list[-1].rules += refinement[i].rules
                new_programs_list[-1].head_predicates = self.refinement_solver.programs_handler.programs_list[i].head_predicates | refinement[i].head_predicates
            ref_programs_handler = ProgramsHandler(new_programs_list, self.programs_handler.instance, None)
            self.refinement_solver = ASPQSolver(ref_programs_handler, self.sub_solvers_settings, False, self.depth+1)

    def construct_assumptions(self):
        self.assumptions = []
        for symbol in self.symbols_defined_in_first_program.keys():
            if symbol in self.current_candidate_symbols_set and symbol.name in self.programs_handler.p(0).head_predicates:
                self.assumptions.append((symbol, True))
            else:
                self.assumptions.append((symbol, False))
