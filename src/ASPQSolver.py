from pathlib import Path
import clingo

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
    #for avoiding rewriting on facts
    instance_program : str
    ctl_programs_list : list
    programs_models: list
    assumptions : list
    symbols_defined_in_programs : dict
    last_model_symbols_list : list
    last_model_symbols_sets : list 
    
    refinement_rewriters : list
    models_found : int
    exists_first: bool
    counterexample_found : int
    model_printer : ModelPrinter
    logger : MyLogger
    settings : SolverSettings
    program_levels : int
    solving_level : int
    iteration : int
    
    def __init__(self, encoding_path, instance_path, solver_settings) -> None:
        self.settings = solver_settings
        encoding_program = ""
        try:
            encoding_program = "\n".join(open(encoding_path).readlines())
        except:
            print("Could not open problem file")
            exit(1)

        if instance_path != "":
            try:
                self.instance_program = "\n".join(open(instance_path).readlines())
            except:
                print("Could not open instance file")
                exit(1)        
        else:
            self.instance_program = ""
        self.programs_handler = ProgramsHandler(encoding_program, self.settings.relaxed_solving)
        self.program_levels = len(self.programs_handler.original_programs_list)-1
        self.ctl_programs_list = [clingo.Control() for _ in range(self.program_levels)]

        self.assumptions = [[] for _ in range(self.program_levels +1)]
        self.last_model_symbols_list = [None for _ in range(self.program_levels +1)]
        self.last_model_symbols_sets = [set() for _ in range(self.program_levels +1)]

        self.refinement_rewriters = [None for _ in range(self.program_levels)]
        # self.reduct_no_constraint_rewriters = [None for _ in range(self.program_levels)]
        self.symbols_defined_in_programs = dict()
        self.models_found = 0
        self.counterexample_found = 0
        self.model_printer = PositiveModelPrinter() if not self.settings.constraint_print else ConstraintModelPrinter()
        self.logger = self.settings.logger
        self.exists_first = self.programs_handler.split_rewriter.exists_first()
        self.iteration = 1


    def ground_and_construct_choice_interfaces(self):
        choice = []
        
        #1-ASP(Q) programs always have a constraint program - it is created without rules when a constraint program is not parsed
        if self.program_levels == 1:
            self.ctl_programs_list[0].add("\n".join(self.programs_handler.p(0).rules))
            self.logger.print(f"Added program {self.programs_handler.p(0).rules} to ctl 0")
            if self.programs_handler.last_exists():
                self.logger.print(f"Added program {self.programs_handler.c().rules} to ctl 0")
                self.ctl_programs_list[0].add("\n".join(self.programs_handler.c().rules))
            else:
                self.logger.print(f"Added program {self.programs_handler.neg_c().rules} to ctl 0")
                self.ctl_programs_list[0].add("\n".join(self.programs_handler.neg_c().rules))
            if self.instance_program != "":
                self.ctl_programs_list[0].add(self.instance_program)
            self.ctl_programs_list[0].ground()
            self.logger.print("Grounded ctl 0")
            prg = self.programs_handler.p(0)
            head_predicates = prg.head_predicates
            #find symbols defined in this program - those that have as predicate one among head_predicates
            self.symbols_defined_in_programs[prg.name] = dict()
            for atom in self.ctl_programs_list[0].symbolic_atoms:
                if atom.symbol.name in head_predicates:
                    self.symbols_defined_in_programs[prg.name][atom.symbol]=None
            
            return
        
        for i in range(0, self.program_levels):
            # add constraint program to counterexample ctl
            if i == self.program_levels-1:
                if self.programs_handler.last_exists():
                    self.ctl_programs_list[i].add("\n".join(self.programs_handler.c().rules))
                    self.logger.print(f"added to ctl {i} program: {"\n".join(self.programs_handler.c().rules)}")
                else:
                    self.logger.print(f"added to ctl {i} program: {"\n".join(self.programs_handler.neg_c().rules)}")
                    self.ctl_programs_list[i].add("\n".join(self.programs_handler.neg_c().rules))
            # add program P_i to ctl
            self.ctl_programs_list[i].add("\n".join(self.programs_handler.p(i).rules))
            self.logger.print(f"added to ctl {i} program: {"\n".join(self.programs_handler.p(i).rules)}")
            if self.instance_program != "":
                self.ctl_programs_list[i].add(self.instance_program)
            self.ctl_programs_list[i].ground()
            self.logger.print(f"Grounded ctl {i}")
            disjoint = True
            prg = self.programs_handler.p(i)
            head_predicates = prg.head_predicates
            #find symbols defined in this program - those that have as predicate one among head_predicates
            self.symbols_defined_in_programs[prg.name] = dict()
            for atom in self.ctl_programs_list[i].symbolic_atoms:
                if atom.symbol.name in head_predicates:
                    self.symbols_defined_in_programs[prg.name][atom.symbol]=None
                    choice.append(str(atom.symbol))
                    disjoint = False
            #add choice in the next program
            if not disjoint:
                choice_str = ""
                if len(choice) > 0:
                    choice_str = ";".join(choice)
                #last program adds no choice - there is no ctl next and it is the counterexample ctl
                if i != self.program_levels-1:
                    choice_str = "{"+ choice_str + "}."
                    self.logger.print(f"added choice to ctl {i}: {choice_str}")
                    self.ctl_programs_list[i+1].add(choice_str)
    
    def on_model(self, model):
        self.last_model_symbols_list[self.solving_level] = model.symbols(shown=True)

    def finished_solve(self, result):
        if not result.unsatisfiable:
            self.last_model_symbols_sets[self.solving_level].clear()
            for symbol in self.last_model_symbols_list[self.solving_level]:
                self.last_model_symbols_sets[self.solving_level].add(symbol)


    #add quantified answer set as constraint for enabling enumeration        
    def add_model_as_constraint(self):
        constraint = ":-"
        for symbol in self.symbols_defined_in_programs["1"].keys():
            if symbol in self.last_model_symbols_sets[0]:
                constraint += f"{symbol},"

            else:
                constraint += f"not {symbol},"

        constraint = constraint[:-1]
        constraint += "."
        self.logger.print(f"Adding constraint: {constraint}")
        self.ctl_programs_list[0].add(f"constraint_{self.models_found}",[], constraint)
        self.ctl_programs_list[0].ground([(f"constraint_{self.models_found}", [])])
        

    def print_projected_model(self):
        self.model_printer.print_model(self.last_model_symbols_sets[0], self.symbols_defined_in_programs["1"])
        

    def exit_sat(self):
        if self.exists_first:
            print(f"Models found: {self.models_found}")
        self.logger.print(f"Counterexample found in the search: {self.counterexample_found}")
        print("ASPQ SAT")
        exit(10)
    
    def exit_unsat(self):
        self.logger.print(f"Counterexample found in the search: {self.counterexample_found}")
        print("ASPQ UNSAT")
        exit(20)

    #solve function for ASPQ with n levels
    def solve_n_levels(self):
        for i in range(0, self.program_levels-1):
            to_rewrite_programs = []
            for j in range(i+1, self.program_levels):
                to_rewrite_programs.append(self.programs_handler.original_programs_list[j])
            
            #constraint programs are reversed since a refinement rewriter for \exists is actually rewriting in the \forall program
            #before and vice versa
            if self.programs_handler.p(i).program_type == ProgramQuantifier.EXISTS:
                to_rewrite_programs.append(self.programs_handler.c())
            else:
                to_rewrite_programs.append(self.programs_handler.neg_c())
            self.refinement_rewriters[i] = RefinementRewriter(to_rewrite_programs, False)
            self.refinement_rewriters[i].compute_placeholder_program()
        
        self.ground_and_construct_choice_interfaces()
        
        while self.models_found < self.settings.n_models or self.settings.enumeration:
            satisfiable = self.recursive_cegar(0)
            if satisfiable:
                if self.exists_first:
                    self.print_projected_model()
                    self.models_found += 1
                    if self.models_found == self.settings.n_models:
                        self.exit_sat()
                    self.add_model_as_constraint()
                else:
                    self.exit_sat()
            else:
                #program starts with forall and is unsat
                if not self.exists_first:
                    self.exit_unsat()
                
                #program starts with exists and therefore there might be models already found
                #the exit code should depend also on these
                if self.models_found > 0:
                    self.exit_sat()
                else:
                    self.exit_unsat()


    def recursive_cegar(self, i):
        self.solving_level = i

        if self.program_levels == 1:
            # Program is \exists P_1:C or \forall P_1:C (with C possibly empty)
            result = self.ctl_programs_list[0].solve(on_model=self.on_model, on_finish=self.finished_solve)
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
                self.solving_level = 0
                #add model M_1 of P_1 as assumption
                self.assumptions[0] = []
                prg = self.programs_handler.p(0)
                self.logger.print("Searching for candiate")
                result = self.ctl_programs_list[0].solve(on_model=self.on_model, on_finish=self.finished_solve)
                if result.unsatisfiable:
                    #forall wins if P_1 has no sm
                    #exist looses if P_1 has no sm
                    return True if self.programs_handler.last_exists() else False
                else:
                    self.logger.print(f"Found candiate {self.last_model_symbols_list}")
                    for symbol in self.symbols_defined_in_programs[prg.name].keys():
                        if symbol in self.last_model_symbols_sets[0] and symbol.name in prg.head_predicates:
                            self.assumptions[0].append((symbol, True))
                        else:
                            self.assumptions[0].append((symbol, False))
                    #search for counterexample
                    self.solving_level += 1
                    self.logger.print(f"Searching for counterexample {self.assumptions[0]}")
                    result = self.ctl_programs_list[1].solve(assumptions=self.assumptions[0], on_model=self.on_model, on_finish=self.finished_solve)
                    
                    #winning move for the first quantifier - no recursive call for 2-ASPQ
                    if result.unsatisfiable:
                        self.logger.print("No counterexample found")
                        #forall wins if P_2 \cup \neg C has no sm
                        #exists looses if P_2 \cup C has no sm 
                        return False if self.programs_handler.last_exists() else True
                    self.logger.print("Counterexample found")
                    rewriter = self.refinement_rewriters[self.solving_level-1]
                    rewriter.rewrite(self.last_model_symbols_sets[1], self.iteration)
                    # counterexample_facts = ""
                    # for symbol in self.symbols_defined_in_programs[self.programs_handler.p(1).name].keys():
                    #     if symbol in self.last_model_symbols_sets[1] and symbol.name in self.programs_handler.p(1).head_predicates:
                    #         new_symbol = clingo.Function(symbol.name + rewriter.suffix_n, symbol.arguments, symbol.positive)
                    #         counterexample_facts = counterexample_facts + str(new_symbol) + "."
                    self.ctl_programs_list[0].add(f"iteration_{self.iteration}", [], rewriter.rewritten_program)
                    self.logger.print(f"Result of refinement: {rewriter.rewritten_program}")
                    self.ctl_programs_list[0].ground([(f"iteration_{self.iteration}", [])])
                    self.iteration+=1
        else:
            self.logger.print(f"Inside recursive cegar at level {i}")
            while True:
                if self.solving_level == self.program_levels:
                    print("Called solve for last level")
                    #search for CE
                    #print(f"ASSUMPTIONS: {self.assumptions}")
                    #search for counterexample
                    #assumptions are the union of assumptions for all programs that appear before the program at the current level
                    expanded_assumptions = [atom for assumpt in self.assumptions[0:self.solving_level] for atom in assumpt]
                    print(f"Adding assumptions: {expanded_assumptions}")
                    result = self.ctl_programs_list[len(self.ctl_programs_list) -1].solve(assumptions=expanded_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                    
                    #no counterexample - winning move found
                    if result.unsatisfiable:
                        print("No counterexample")
                        return True
                    #refine abstraction
                    else:
                        print(f"Counterexample found: {self.last_model_symbols_list[i]}")
                        self.ce_found = True
                        return False
                        # self.refine_abstractions()
                else:
                    print("Called solve for non-last level")
                    #find model and construct assumptions
                    #assumptions are the union of assumptions for all programs that appear before the program at the current level
                    expanded_assumptions = [atom for assumpt in self.assumptions[0:self.solving_level] for atom in assumpt]
                    print(f"Adding assumptions: {expanded_assumptions}")
                    result = self.ctl_programs_list[self.solving_level].solve(assumptions=expanded_assumptions, on_model=self.on_model, on_finish=self.finished_solve)
                    #no candiate found - no candidate winning move and thus I need to refine
                    if result.unsatisfiable:
                        print("No candidate found")
                        return False
                    #candidate found
                    else:
                        print(f"Candidate found: {self.last_model_symbols_list[i]}")
                        #clear assumptions for the current level
                        self.assumptions[self.solving_level] = []
                        prg = self.programs_handler.p(self.solving_level)
                        for symbol in self.symbols_defined_in_programs[prg.name].keys():
                            if symbol in self.last_model_symbols_sets[self.solving_level] and symbol.name in prg.head_predicates:
                                self.assumptions[self.solving_level].append((symbol, True))
                            else:
                                self.assumptions[self.solving_level].append((symbol, False))
                        res = self.recursive_cegar(i+1)
                        self.solving_level = i
                        #winning move for the next quantifier
                        if not res: 
                            print(f"No winning move for the {i+1} quantifier")
                            return True
                        else:
                            print(f"Winning move for the {i+1} quantifier, I have to search for another candidate")
                            self.refine_abstractions()

                    
    def refine_abstractions(self):
        self.refinement_rewriters[self.solving_level].rewrite()
        self.iteration += 1
        
        