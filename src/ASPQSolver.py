from pathlib import Path
import clingo

from .SolverStatistics import SolverStatistics

from .CounterexampleRewriter import CounterexampleRewriter
from .RefinementRewriter import RefinementRewriter
from .SolverSettings import SolverSettings
from .MyProgram import ProgramQuantifier
from .ConstraintModelPrinter import ConstraintModelPrinter
from .ModelPrinter import ModelPrinter
from .MyLogger import MyLogger
from .PositiveModelPrinter import PositiveModelPrinter
from .ProgramsHandler import ProgramsHandler

class ASPQSolver:
    programs_handler : ProgramsHandler
    ctl_move : clingo.Control
    ctl_countermove : clingo.Control
    assumptions : list
    symbols_defined_in_first_program : dict
    last_model : clingo.solving._SymbolSequence
    last_model_symbols_set : set
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

    def __init__(self, programs_handler, solver_settings, main_solver, depth):
        self.programs_handler = programs_handler
        self.depth = depth
        self.choice_str = ""
        self.settings = solver_settings
        #sub solvers are always required to compute one model, inherit the same debug flag as the parent,
        #never print the model as a constraint since no enumeration is needed, apply ground transformations iff the current solver does
        self.sub_solvers_settings = SolverSettings(1, self.settings.debug, False, self.settings.ground_transformation)
        self.program_levels = len(self.programs_handler.original_programs_list) -1
        self.ctl_move = clingo.Control()
        self.ctl_countermove = clingo.Control()
        self.assumptions = []
        self.counterexample_rewriter = None
        self.refinement_rewriter = None
        self.models_found = 0
        self.model_printer = PositiveModelPrinter() if not self.settings.constraint_print else ConstraintModelPrinter()
        self.logger = self.settings.logger
        self.exists_first = self.programs_handler.exists_first()
        self.main_solver = main_solver
        if self.program_levels > 2:
            #define counterexample and refinement solvers
            self.counterexample_solver = None
            self.refinement_solver =  None
        self.last_model_symbols_set = set()
        self.symbols_defined_in_first_program = dict()

    def ground_and_construct_choice_interfaces(self):
        choice = []
        self.ctl_move = clingo.Control()
        self.ctl_move.add(self.programs_handler.p(0).rules)
        self.logger.print(f"Added choice to ctl move {self.choice_str}")
        self.ctl_move.add(self.choice_str)
        if self.programs_handler.instance != "":
            self.ctl_move.add(self.programs_handler.instance)
        
        #1-ASP(Q) programs always have a constraint program - it is created without rules when a constraint program is not parsed
        if self.program_levels == 1:
            if self.programs_handler.last_exists():
                self.logger.print(f"{self.depth * "\t"}Added program {self.programs_handler.c().rules} to ctl 0")
                self.ctl_move.add(self.programs_handler.c().rules)
            else:
                self.logger.print(f"{self.depth * "\t"}Added program {self.programs_handler.neg_c().rules} to ctl 0")
                self.ctl_move.add(self.programs_handler.neg_c().rules)
            self.ctl_move.ground()
            for atom in self.ctl_move.symbolic_atoms:
                if atom.symbol.name in self.programs_handler.p(0).head_predicates:
                    self.symbols_defined_in_first_program[atom.symbol] = None
                    
            self.logger.print(f"{self.depth * "\t"}Grounded ctl 0")        
            return
        else:
            self.ctl_move.ground()
            choice = []
            disjoint = True
            for atom in self.ctl_move.symbolic_atoms:
                if atom.symbol.name in self.programs_handler.p(0).head_predicates:
                    self.symbols_defined_in_first_program[atom.symbol] = None
                    choice.append(str(atom.symbol))
                    disjoint = False

            #add choice in the next program
            if not disjoint:
                if len(choice) > 0:
                    sub_choice_str = ";".join(choice) 
                    sub_choice_str = "{"+ sub_choice_str + "}. "
                    self.choice_str += sub_choice_str
                    self.logger.print(f"{self.depth * "\t"}Constructed choice: {self.choice_str}")

            if self.program_levels == 2:
                self.ctl_countermove = clingo.Control()
                self.logger.print(f"{self.depth * "\t"}added choice to countermove ctl: {self.choice_str}")
                self.ctl_countermove.add(self.choice_str)
                self.ctl_countermove.add(self.programs_handler.p(1).rules)
                if self.programs_handler.last_exists():
                    self.ctl_countermove.add(self.programs_handler.c().rules)
                    self.logger.print(f"{self.depth * "\t"}added to countermove ctl program: {self.programs_handler.c().rules}")
                else:
                    self.logger.print(f"{self.depth * "\t"}added to countermove ctl program: {self.programs_handler.neg_c().rules}")
                    self.ctl_countermove.add(self.programs_handler.neg_c().rules)
                self.ctl_countermove.ground()

    def on_model(self, model):
        self.last_model= model.symbols(shown=True)

    def finished_solve(self, result):
        if not result.unsatisfiable:
            self.last_model_symbols_set.clear()
            for symbol in self.last_model:
                self.last_model_symbols_set.add(symbol)


    #add quantified answer set as constraint for enabling enumeration        
    def add_model_as_constraint(self):
        constraint = ":-"
        for symbol in self.symbols_defined_in_first_program.keys():
            if symbol in self.last_model_symbols_set:
                constraint += f"{symbol},"

            else:
                constraint += f"not {symbol},"

        constraint = constraint[:-1]
        constraint += "."
        self.logger.print(f"{self.depth * "\t"}Adding constraint: {constraint}")
        self.ctl_move.add(f"constraint_{self.models_found}",[], constraint)
        self.ctl_move.ground([(f"constraint_{self.models_found}", [])])

    def print_projected_model(self):
        self.model_printer.print_model(self.last_model_symbols_set, self.symbols_defined_in_first_program)
        
    #solve function for ASPQ with n levels
    def solve_n_levels(self, external_assumptions, choice_str):
        SolverStatistics().aspq_solvers_calls += 1
        self.choice_str = choice_str
        self.external_assumptions = external_assumptions

        self.ground_and_construct_choice_interfaces()

        while self.models_found < self.settings.n_models or self.settings.enumeration:
            satisfiable = self.recursive_cegar()
            if satisfiable:
                if self.exists_first:
                    self.models_found += 1
                    if self.main_solver:
                        self.print_projected_model()
                        SolverStatistics().model_found()
                        #empty model is unique if it exists - no other models can be
                        if len(self.last_model) == 0:
                            return True
                    if self.models_found == self.settings.n_models:
                        return True
                    self.add_model_as_constraint()
                else:
                    return True
            else:
                #program starts with forall and is unsat
                if not self.exists_first:
                    return False
                                
                #program starts with exists and therefore there might be models already found
                #the exit code should depend also on these
                if self.models_found > 0:
                    return True
                else:
                    return False

    def recursive_cegar(self):
        if self.program_levels == 1:
            # Program is \exists P_1:C or \forall P_1:C (with C possibly empty)
            result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
            if result.unsatisfiable:
                #exists looses if P_1 \cup C unsat
                #forall wins if P_1 \cup \neg C unsat
                return False if self.programs_handler.last_exists() else True
            #exists wins if P_1 \cup C sat
            #forall looses if P_1 \cup \neg C sat            
            return True if self.programs_handler.last_exists() else False
        #\exists P_1 \forall P_2 : C or
        #\forall P_1 \exists P_2 : C
        elif self.program_levels == 2:
            while True:
                #add model M_1 of P_1 as assumption
                self.assumptions = []
                self.logger.print(f"{self.depth * "\t"}Searching for candiate")
                result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                if result.unsatisfiable:
                    #forall wins if P_1 has no sm
                    #exist looses if P_1 has no sm
                    return True if self.programs_handler.forall_first() else False
                else:
                    self.logger.print(f"{self.depth * "\t"}Found candiate {self.last_model}")
                    self.construct_assumptions()
                    #search for counterexample
                    self.logger.print(f"{self.depth * "\t"}Searching for counterexample")
                    result = self.ctl_countermove.solve(assumptions=self.assumptions + self.external_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                    
                    #winning move for the first quantifier - no recursive call for 2-ASPQ
                    if result.unsatisfiable:
                        self.logger.print(f"{self.depth * "\t"}No counterexample found")
                        #forall wins if P_2 \cup \neg C has no sm
                        #exists looses if P_2 \cup C has no sm
                        return False if self.programs_handler.last_exists() else True
                    self.logger.print(f"{self.depth * "\t"}Counterexample found {self.last_model}")
                    SolverStatistics().conterexample_found += 1
                    if self.refinement_rewriter is None:
                        self.refinement_rewriter = RefinementRewriter([self.programs_handler.p(1)], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.ground_transformation)
                        self.refinement_rewriter.compute_placeholder_program()
                    self.refinement_rewriter.rewrite(self.last_model, SolverStatistics().solvers_iterations)
                    refine_program = self.refinement_rewriter.refined_program()
                    self.ctl_move.add(f"iteration_{SolverStatistics().solvers_iterations}", [], refine_program)
                    self.logger.print(f"{self.depth * "\t"}Result of refinement: {refine_program}")
                    self.ctl_move.ground([(f"iteration_{SolverStatistics().solvers_iterations}", [])])
                    SolverStatistics().iteration_done()
        else:
            self.logger.print(f"{self.depth * "\t"}Inside recursive cegar for n-ASPQ with n >=3")
            while True:
                self.assumptions = []
                if self.refinement_solver is None:
                    #on the first iteration is just a solve on the outermost program
                    result = self.ctl_move.solve(assumptions = self.external_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                    if result.unsatisfiable:
                        #no move, current quantifier looses
                        return False if self.exists_first else True
                    else: 
                        self.logger.print(f"{self.depth * "\t"}Found candiate {self.last_model}")
                        self.construct_assumptions()
                else:
                    if self.program_levels > 3:
                        satisfiable = self.refinement_solver.solve_n_levels(self.external_assumptions, self.choice_str)
                        SolverStatistics().aspq_solvers_calls += 1
                                                
                        if not satisfiable:
                            return False if self.exists_first else True
                        else:
                            self.refinement_rewriter.construct_assumptions()
                            self.logger.print(f"{self.depth * "\t"}Found candiate {self.last_model}")
                    else:
                        result = self.ctl_move.solve(assumptions=self.external_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                        if result.unsatisfiable:
                            return False if self.exists_first else True
                        else:
                            self.logger.print(f"{self.depth * "\t"}{self.depth * "\t"}Found candiate {self.last_model}")


                if self.counterexample_rewriter is None:
                    self.counterexample_rewriter = CounterexampleRewriter(self.programs_handler.original_programs_list[1:len(self.programs_handler.original_programs_list)-1], self.programs_handler.c(), self.programs_handler.neg_c())
                
                self.counterexample_rewriter.rewrite(self.last_model, self.symbols_defined_in_first_program, self.programs_handler.p(0).head_predicates)
                #this is always an ASPQ program with two or more levels
                ce_programs_handler = ProgramsHandler(self.counterexample_rewriter.rewritten_program(), self.programs_handler.instance)
                self.counterexample_solver = ASPQSolver(ce_programs_handler, self.sub_solvers_settings, False, self.depth +1)
                
                self.construct_assumptions()
                satisfiable = self.counterexample_solver.solve_n_levels(self.external_assumptions + self.assumptions, self.choice_str)
                
                #no counterexample
                if not satisfiable and self.programs_handler.forall_first():
                    return False
                    
                if not satisfiable and self.programs_handler.exists_first():
                    return True
                
                #a counterexample was found
                SolverStatistics().aspq_solvers_calls += 1
                if self.refinement_rewriter is None:
                    self.refinement_rewriter = RefinementRewriter(self.programs_handler.original_programs_list[1:len(self.programs_handler.original_programs_list)-1], self.programs_handler.c(), self.programs_handler.neg_c(), self.settings.ground_transformation)
                    self.refinement_rewriter.compute_placeholder_program()
                self.refinement_rewriter.rewrite(self.counterexample_solver.last_model, SolverStatistics().solvers_iterations)
                #program with potentially first quantifiers collapsed and the or applied to remaining quantifiers (and also C)
                refinement = self.refinement_rewriter.refined_program()
                
                #refinement is an ASP program and can be directly added to the ctl_move
                if type(refinement) == str:
                    self.ctl_move.add(f"iteration_{SolverStatistics().solvers_iterations}", [], refinement)
                    self.ctl_move.ground([(f"iteration_{SolverStatistics().solvers_iterations}", [])])
                else: #refinement is an ASPQ
                    if self.refinement_solver == None:
                        refinement_handler =  ProgramsHandler(refinement, self.programs_handler.instance)
                        #add rules from P_1 into refinement which containts only programs from P_2
                        refinement[0].rules += self.programs_handler.p(0).rules
                        self.refinement_solver = ASPQSolver(refinement_handler, self.sub_solvers_settings, False, self.depth +1)
                    else:
                        assert len(refinement_handler.original_programs_list) == len(self.refinement_solver.programs_handler.original_programs_list)
                        #update programs handler of of refinement_solver by extending programs with result of refinement
                        for i in range(len(refinement_handler.original_programs_list)):
                            self.refinement_solver.programs_handler.original_programs_list[i].rules += refinement_handler.original_programs_list[i].rules
                SolverStatistics().iteration_done()
                
    def construct_assumptions(self):
        self.assumptions = []
        for symbol in self.symbols_defined_in_first_program.keys():
            if symbol in self.last_model_symbols_set and symbol.name in self.programs_handler.p(0).head_predicates:
                self.assumptions.append((symbol, True))
            else:
                self.assumptions.append((symbol, False))

    def extend_with_refinement(self, refinement):
        assert not self.ctl_move is None
        # self.ctl_move.add(f"refinement_{SolverStatistics().solvers_iterations}", [], self.programs_handler.p(0))
        #eachh solver has a move ctl. If I 
        #If |\Pi| = 10, then ref(\Pi, M_1) [P_1 \cup P_2^{M_2} \cup P_3^{v}, \box_1 P_4, box_2 P_5, ..., \box_j P_{10}^{v} : C^*]
        #
        if not self.refinement_solver is None:
            self.refinement_solver.extend_control(refinement[1::])
        else: #reached ASPQ program of length 2
            assert self.program_levels == 2
            #adding refinement for 2-ASPQ which should add 
            refinement_rules = refinement[0].rules + refinement[1].rules
            self.ctl_countermove.add(f"refinement_{SolverStatistics().solvers_iterations}", [], )

