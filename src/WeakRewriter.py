

from .WeakConstraint import WeakConstraint
from .SolverSettings import SolverSettings
from .ProgramsHandler import ProgramsHandler
from .FlipConstraintRewriter import FlipConstraintRewriter
from .CheckRewriter import CheckRewriter
from .QuantifiedProgram import ProgramQuantifier, QuantifiedProgram
from .OrProgramRewriter import OrProgramRewriter
from clingo.ast import parse_string

class WeakRewriter:

    original_programs : list
    rewritten_programs : list
    or_predicate : str
    rewritten_program_contains_weak : bool
    rewrite_without_weaks : bool

    def __init__(self, split_program_rewriter, rewrite_without_weaks):
        self.split_program_rewriter = split_program_rewriter

        self.original_programs = split_program_rewriter.programs
        self.rewritten_programs = []
        self.rewritten_program_contains_weak = False
        self.rewrite_without_weaks = rewrite_without_weaks
            
        #program of more than two levels is not allowed to contain weak
        if len(self.original_programs) > 3:
            for program in self.original_programs:
                if program.contains_weak():
                    raise Exception("This solver supports ASP(Q) with weak up to the second level")    
        if not self.rewrite_without_weaks:
            #collapse plain uniform subprograms
            rewritten = True
            while rewritten:
                rewritten = False
                for index in range(1,len(self.original_programs)):
                    if self.col1(index):
                        rewritten = True
                        break

            #uniform not-plain plain rewriting done
            #only one program is left with weak constraints
            if len(self.original_programs) == 1:
                self.rewritten_program_contains_weak = self.original_programs[0].contains_weak() #second program is constraint
                return
            elif len(self.original_programs) == 2:
                #this is either \exists, c; \forall c or \exists_weak, c; \forall_weak c
                if self.original_programs[0].contains_weak():
                    if self.original_programs[0].exists():
                        self.rewrite_exists_weak_c()
                    else:
                        self.rewrite_forall_weak_c()
            else: #rewriting uniform not-plain plain did not produce an ASP program - either \Pi is alternating or uniform and <(not)plain, not plain>
                self.rewrite_uniform_not_plain_plain()
                self.rewrite()
        else:
            # print("Rewriting weak constraints")
            self.rewrite_no_cegar()
            for program in self.original_programs:
                print(program)
            # print("Rewriting finished, terminating...")
            exit(0)

    def rewrite_no_cegar(self):
        self.rewritings = [self.col1, self.col2, self.col3, self.col4, self.col5]
        transfomation_done = True
        while(transfomation_done):
            transfomation_done = False
            for rewriting in self.rewritings:
                rewritten = False
                my_range = range(len(self.original_programs)-2, 0, -1) if rewriting != self.col4 and rewriting != self.col5 else range(len(self.original_programs)-2, -1, -1)
                for program_idx in my_range:
                    if rewriting(program_idx):
                        transfomation_done = True
                        rewritten = True
                        break
                if rewritten:
                    break
            

    def col1(self, index):
        second_program = self.original_programs[index]
        second_program_name = second_program.name
        second_program_type = second_program.program_type
        second_program_plain = not second_program.contains_weak()

        first_program = self.original_programs[index-1]
        first_program_name = first_program.name
        first_program_type = first_program.program_type
        first_program_plain = not first_program.contains_weak()
        if first_program_type == second_program_type and first_program_plain and second_program_plain:
            # print(f"Applying col1 to index {index}")
            collapsed_programs = QuantifiedProgram(f"{self.original_programs[index-1].rules}\n{self.original_programs[index].rules}", [], first_program_type, f"{first_program_name}_{second_program_name}", second_program.head_predicates | first_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [collapsed_programs] + self.original_programs[index+1::]
            self.update_programs()
            return True
        else:
            return False

            
    def col2(self, index):
        second_program = self.original_programs[index]
        second_program_name = second_program.name
        second_program_type = second_program.program_type
        second_program_plain = not second_program.contains_weak()

        first_program = self.original_programs[index-1]
        first_program_name = first_program.name
        first_program_type = first_program.program_type
        first_program_plain = not first_program.contains_weak()
        assert not first_program is None
        if first_program_type == ProgramQuantifier.EXISTS and second_program_type == ProgramQuantifier.EXISTS and not first_program_plain and second_program_plain:
            # print(f"Applying col2 to index {index}")
            unsat_predicate_name = f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{second_program_name}"
            or_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, second_program)
            or_rewriter.rewrite("", None)
            unsat_choice = "{" + unsat_predicate_name + "}."
            weak_constraints = first_program.weak_constraints
            weak_constraints.append(WeakConstraint(unsat_predicate_name, 1, SolverSettings.WEAK_NO_MODEL_LEVEL, []))
            rewritten_plain_program = QuantifiedProgram(f"{first_program.rules}\n{or_rewriter.rewritten_program}\n{unsat_choice}", weak_constraints, ProgramQuantifier.EXISTS, f"{first_program_name}_{second_program_name}", second_program.head_predicates | first_program.head_predicates | set([unsat_predicate_name]))
            original_constraint_program = self.original_programs[-1]

            #rewriting last program (P_n - there is only C after)
            if index == len(self.original_programs) -2:
                assert self.original_programs[index+1].program_type == ProgramQuantifier.CONSTRAINTS
                rewritten_constraint_program = QuantifiedProgram(f"{original_constraint_program.rules}\n:-{unsat_predicate_name}.", [], original_constraint_program.program_type, original_constraint_program.name, original_constraint_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_constraint_program]

            elif index == len(self.original_programs) -3: #there is exactly one forall after P_i
                rewritten_constraint_program = QuantifiedProgram(f"{original_constraint_program.rules}\n:-{unsat_predicate_name}.", [], original_constraint_program.program_type, original_constraint_program.name, original_constraint_program.head_predicates)
                assert self.original_programs[index+1].program_type == ProgramQuantifier.FORALL
                next_forall_program = self.original_programs[index+1]
                or_next_forall_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, next_forall_program)
                or_next_forall_rewriter.rewrite("", None)
                rewritten_next_forall_program = QuantifiedProgram(or_next_forall_rewriter.rewritten_program, [], ProgramQuantifier.FORALL, next_forall_program.name, next_forall_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_next_forall_program] + [rewritten_constraint_program]
            else: #there is at least one forall and one exists after P_i
                assert self.original_programs[index+1].program_type == ProgramQuantifier.FORALL and self.original_programs[index+2].program_type == ProgramQuantifier.EXISTS
                next_forall_program = self.original_programs[index+1]
                next_exists_program = self.original_programs[index+2]
                or_next_forall_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, next_forall_program)
                or_next_forall_rewriter.rewrite("", None)
                rewritten_next_forall_program = QuantifiedProgram(or_next_forall_rewriter.rewritten_program, [], ProgramQuantifier.FORALL, next_forall_program.name, next_forall_program.head_predicates)
                next_exists_program_rewritten = QuantifiedProgram(f"{next_exists_program.rules}\n:-{unsat_predicate_name}{next_exists_program.name}." , next_exists_program.weak_constraints, ProgramQuantifier.EXISTS, next_exists_program.name, next_exists_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_next_forall_program] + [next_exists_program_rewritten] + self.original_programs[index+3:len(self.original_programs)]
            self.update_programs()
            return True
        return False


    def col3(self, index):
        second_program = self.original_programs[index]
        second_program_name = second_program.name
        second_program_type = second_program.program_type
        second_program_plain = not second_program.contains_weak()

        first_program = self.original_programs[index-1]
        first_program_name = first_program.name
        first_program_type = first_program.program_type
        first_program_plain = not first_program.contains_weak()
        if first_program_type == ProgramQuantifier.FORALL and second_program_type == ProgramQuantifier.FORALL and not first_program_plain and second_program_plain:
            # print(f"Applying col3 to index {index}")
            unsat_predicate_name = f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{second_program_name}"
            or_p2_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, second_program)
            or_p2_rewriter.rewrite("", None)
            unsat_choice = "{" + unsat_predicate_name + "}."
            weak_constraints = first_program.weak_constraints
            weak_constraints.append(WeakConstraint(unsat_predicate_name, 1, SolverSettings.WEAK_NO_MODEL_LEVEL, []))
            rewritten_plain_program = QuantifiedProgram(f"{self.original_programs[index-1].rules}\n{or_p2_rewriter.rewritten_program}\n{unsat_choice}", weak_constraints, ProgramQuantifier.FORALL, f"{first_program_name}_{second_program_name}", second_program.head_predicates | first_program.head_predicates | set([unsat_predicate_name]))
            original_constraint_program = self.original_programs[-1]

            #rewriting last program (P_n - there is only C after)
            if index == len(self.original_programs) -2:
                assert self.original_programs[index+1].program_type == ProgramQuantifier.CONSTRAINTS
                constraint_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, original_constraint_program)
                constraint_rewriter.rewrite("", None)
                rewritten_constraint_program = QuantifiedProgram(f"{constraint_rewriter.rewritten_program}", [], ProgramQuantifier.CONSTRAINTS, original_constraint_program.name , original_constraint_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_constraint_program]

            elif index == len(self.original_programs) -3: #there is exactly one forall after P_i
                assert self.original_programs[index+1].program_type == ProgramQuantifier.EXISTS
                constraint_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, original_constraint_program)
                constraint_rewriter.rewrite("", None)
                rewritten_constraint_program = QuantifiedProgram(f"{constraint_rewriter.rewritten_program}", [], ProgramQuantifier.CONSTRAINTS, original_constraint_program.name , original_constraint_program.head_predicates) 
                next_exists_program = self.original_programs[index+1]
                or_next_exists_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, next_exists_program)
                or_next_exists_rewriter.rewrite("", None)
                rewritten_next_exists_program = QuantifiedProgram(or_next_exists_rewriter.rewritten_program, [], ProgramQuantifier.EXISTS, next_exists_program.name, next_exists_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_next_exists_program] + [rewritten_constraint_program]
            else: #there is at least one forall and one exists after P_i
                assert self.original_programs[index+1].program_type == ProgramQuantifier.EXISTS and self.original_programs[index+2].program_type == ProgramQuantifier.FORALL
                next_exists_program = self.original_programs[index+1]
                next_forall_program = self.original_programs[index+2]
                or_next_exists_rewriter = OrProgramRewriter(set(), unsat_predicate_name, False, next_exists_program)
                or_next_exists_rewriter.rewrite("", None)
                rewritten_next_exists_program = QuantifiedProgram(or_next_exists_rewriter.rewritten_program, [], ProgramQuantifier.EXISTS, next_exists_program.name, next_exists_program.head_predicates)
                rewritten_next_forall_program = QuantifiedProgram(f"{next_forall_program.rules}\n:-{unsat_predicate_name}{next_forall_program.name}.", next_forall_program.weak_constraints, ProgramQuantifier.FORALL, next_forall_program.name, next_forall_program.head_predicates)
                self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_plain_program] + [rewritten_next_exists_program] + [rewritten_next_forall_program] + self.original_programs[index+3:len(self.original_programs)]
            
            self.update_programs()
            return True
        return False


    def col4(self, index):
        rewriting_program = self.original_programs[index]
        rewriting_program_name = rewriting_program.name
        rewriting_program_type = rewriting_program.program_type

        #current program must be an exists for col4 to be applicable
        if rewriting_program_type != ProgramQuantifier.EXISTS or not rewriting_program.contains_weak():
            return False
        #all programs after the current must be plain
        for i in range(index+1, len(self.original_programs)):
            if self.original_programs[i].contains_weak():
                return False

        check_rewriter = CheckRewriter(rewriting_program, True, True, True)
        check_rewriter.rewrite(True, rewriting_program.name)
        dominated_pred_name = check_rewriter.dominated_predicate_name
        rewritten_rewriting_program = QuantifiedProgram(rewriting_program.rules, [], rewriting_program.program_type, rewriting_program.name, rewriting_program.head_predicates)
        #rewrite program and add one forall level (I am rewriting \exitst_weak P_1 : C)
        if index == len(self.original_programs)-2: #program must be the last one before constraint
            # print(f"Applying col4 to index {index}")
            added_program_head_predicates = set([dominated_pred_name]) | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates
            added_program = QuantifiedProgram(f"{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.FORALL, f"{rewriting_program_name}_col4", added_program_head_predicates)
            constraint_program = self.original_programs[-1]            
            rewritten_constraint_program = QuantifiedProgram(f"{constraint_program.rules}\n:-{dominated_pred_name}.", [], ProgramQuantifier.CONSTRAINTS, constraint_program.name, constraint_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:index] + [rewritten_rewriting_program] + [added_program] + [rewritten_constraint_program]

            self.update_programs()
            return True
        #rewrite first program exploiting second forall program (no extra quantied program)
        elif index == len(self.original_programs)-3:
            assert self.original_programs[index+1].program_type == ProgramQuantifier.FORALL
            # print(f"Applying col4 to index {index}")
            next_forall_program = self.original_programs[index+1]
            or_next_forall_program_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, next_forall_program)
            or_next_forall_program_rewriter.rewrite("", None)
            constraint_program = self.original_programs[-1]
            p2_prime_head_predicates = next_forall_program.head_predicates | rewriting_program.head_predicates | check_rewriter.dominated_program_head_predicates | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates 
            p2_prime_program = QuantifiedProgram(f"{or_next_forall_program_rewriter.rewritten_program}\n{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.FORALL, rewriting_program_name, p2_prime_head_predicates)
            rewritten_constraint_program = QuantifiedProgram(f"{constraint_program.rules}\n:-{dominated_pred_name}.", [], ProgramQuantifier.CONSTRAINTS, constraint_program.name, constraint_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_rewriting_program] + [p2_prime_program] + [rewritten_constraint_program]
            
            self.update_programs()
            return True
        
        else: #the next program is a forall and the next one is an exists
            assert self.original_programs[index+1].program_type == ProgramQuantifier.FORALL and self.original_programs[index+2].program_type == ProgramQuantifier.EXISTS
            # print(f"Applying col4 to index {index}")
            next_forall_program = self.original_programs[index+1]
            or_next_forall_program_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, next_forall_program)
            or_next_forall_program_rewriter.rewrite("", None)
            p2_prime_head_predicates = next_forall_program.head_predicates | check_rewriter.dominated_program_head_predicates | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates 
            p2_prime_program = QuantifiedProgram(f"{or_next_forall_program_rewriter.rewritten_program}\n{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.FORALL, rewriting_program_name, p2_prime_head_predicates)
            next_exists_program = self.original_programs[index+2]
            rewritten_next_exists_program = QuantifiedProgram(f"{next_exists_program.rules}\n:-{dominated_pred_name}.", [], next_exists_program.program_type, next_exists_program.name, next_exists_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_rewriting_program] + [p2_prime_program] + [rewritten_next_exists_program] + self.original_programs[index+3::]
            
            self.update_programs()
            return True

    def col5(self, index):
        rewriting_program = self.original_programs[index]
        rewriting_program_name = rewriting_program.name
        rewriting_program_type = rewriting_program.program_type

        #current program must be a forall for col5 to be applicable
        if rewriting_program_type != ProgramQuantifier.FORALL or not rewriting_program.contains_weak():
            return False
        #all programs after the current must be plain
        for i in range(index+1, len(self.original_programs)):
            if self.original_programs[i].contains_weak():
                return False

        check_rewriter = CheckRewriter(rewriting_program, True, True, True)
        check_rewriter.rewrite(True, rewriting_program.name)
        dominated_pred_name = check_rewriter.dominated_predicate_name

        rewritten_rewriting_program = QuantifiedProgram(rewriting_program.rules, [], rewriting_program.program_type, rewriting_program.name, rewriting_program.head_predicates)
        #rewrite program and add one forall level (I am rewriting \exitst_weak P_1 : C)
        if index == len(self.original_programs)-2: #program must be the last one before constraint
            # print(f"Applying col5 to index {index} -2")
            added_program_head_predicates = set([dominated_pred_name]) | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates
            added_program = QuantifiedProgram(f"{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.EXISTS, f"{rewriting_program_name}_col5", added_program_head_predicates)
            constraint_program = self.original_programs[-1]
            or_constraint_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, constraint_program)
            or_constraint_rewriter.rewrite("", None)
            rewritten_constraint_program = QuantifiedProgram(f"{or_constraint_rewriter.rewritten_program}", [], ProgramQuantifier.CONSTRAINTS, constraint_program.name, constraint_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:index] + [rewritten_rewriting_program] + [added_program] + [rewritten_constraint_program]

            self.update_programs()
            return True
        #rewrite first program exploiting second forall program (no extra quantied program)
        elif index == len(self.original_programs)-3:
            assert self.original_programs[index+1].program_type == ProgramQuantifier.FORALL
            # print(f"Applying col5 to index {index} -3")
            next_exists_program = self.original_programs[index+1]
            or_next_exists_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, next_exists_program)
            or_next_exists_rewriter.rewrite("", None)
            constraint_program = self.original_programs[-1]
            p2_prime_head_predicates = next_exists_program.head_predicates | check_rewriter.dominated_program_head_predicates | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates 
            p2_prime_program = QuantifiedProgram(f"{or_next_exists_rewriter.rewritten_program}\n{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.EXISTS, rewriting_program_name, p2_prime_head_predicates)
            or_constraint_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, constraint_program)
            or_constraint_rewriter.rewrite("", None)
            rewritten_constraint_program = QuantifiedProgram(f"{or_constraint_rewriter.rewritten_program}", [], ProgramQuantifier.CONSTRAINTS, constraint_program.name, constraint_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_rewriting_program] + [p2_prime_program] + [rewritten_constraint_program]
            
            self.update_programs()
            return True
        
        else: #the next program is a forall and the next one is an exists
            assert self.original_programs[index+1].program_type == ProgramQuantifier.EXISTS and self.original_programs[index+2].program_type == ProgramQuantifier.FORALL
            # print(f"Applying col5 to index {index}-4, ...")
            next_exists_program = self.original_programs[index+1]
            or_next_exists_rewriter = OrProgramRewriter(set(), dominated_pred_name, False, next_exists_program)
            or_next_exists_rewriter.rewrite("", None)
            p2_prime_head_predicates = rewriting_program.head_predicates | check_rewriter.dominated_program_head_predicates | check_rewriter.clone_program_rewriter.rewritten_program_head_predicates | check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates | check_rewriter.cost_rewriter.rewritten_program_head_predicates 
            p2_prime_program = QuantifiedProgram(f"{or_next_exists_rewriter.rewritten_program}\n{check_rewriter.clone_program}\n{check_rewriter.cost_program}\n{check_rewriter.clone_cost_program}\n{check_rewriter.dominated_program}", [], ProgramQuantifier.EXISTS, rewriting_program_name, p2_prime_head_predicates)
            next_forall_program = self.original_programs[index+2]
            rewritten_next_forall_program = QuantifiedProgram(f"{next_forall_program.rules}\n:-{dominated_pred_name}.", [], next_forall_program.program_type, next_forall_program.name, next_forall_program.head_predicates)
            self.rewritten_programs = self.original_programs[0:max(index-1, 0)] + [rewritten_rewriting_program] + [p2_prime_program] + [rewritten_next_forall_program] + self.original_programs[index+3::]
            
            self.update_programs()
            return True


    def rewrite_uniform_not_plain_plain(self):
        p_1 = self.original_programs[0]
        p_2 = self.original_programs[1]
        p_1_exists = p_1.exists()
        p_1_opt = p_1.contains_weak()
        p_2_exists = p_2.exists()
        p_2_opt = p_2.contains_weak()
        #collapse uniform not plain plain
        if p_1_exists and p_1_opt and p_2_exists and not p_2_opt:
            self.rewrite_exists_weak_exists()
        elif not p_1_exists and p_1_opt and not p_2_exists and not p_2_opt:
            self.rewrite_forall_weak_forall()

    def rewrite(self):
        #The current program can be:
        #alternating with weaks
        #uniform and <not-plain not-plain>
        #uniform and <plain, not-plain>
        
        if self.rewritten_programs == []:
            self.rewritten_programs = self.original_programs
        p_1 = self.original_programs[0]
        p_2 = self.original_programs[1]

        uniform = True if p_1.program_type == p_2.program_type else False
        p_1_exists = p_1.exists()

        #\exists \exists_weak or \forall \foral_weak - not plain plain problems were already transformed into an asp program
        #\exists_weak \exists_weak and \forall_weak \forall_weak are also possible but are treated in the same way
        if uniform:
            if p_1_exists:
                self.rewrite_exists_exists_weak()
            else:
                self.rewrite_forall_forall_weak()

        #else: alternating programs are directly handled by the solver 


    def rewrite_exists_weak_c(self):
        # print("Rewriting an exists weak c program")
        c = self.original_programs[1]

        flipConstraintRewriter = FlipConstraintRewriter(f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}", False)
        parse_string(c.rules, lambda stm: (flipConstraintRewriter(stm)))
        weak_constraint = f":~{SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}. [{SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"
        flipped_constraint = "\n".join(flipConstraintRewriter.program)
        flipped_constraint_with_weak = f"{flipped_constraint}\n{weak_constraint}"
        
        dummy_fact = f"{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}.\n:~{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}. [{SolverSettings.WEIGHT_FOR_DUMMY_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"

        self.rewritten_programs = [QuantifiedProgram(f"{self.original_programs[0].rules}\n{flipped_constraint_with_weak}\n{dummy_fact}",  self.original_programs[0].weak_constraints, ProgramQuantifier.EXISTS, "", self.original_programs[0].head_predicates | self.original_programs[1].head_predicates | set([f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}"])), QuantifiedProgram("", [], ProgramQuantifier.CONSTRAINTS, "c", set())]
        self.update_programs()

    def rewrite_forall_weak_c(self):
        # print("Rewriting a forall weak c program")
        c = self.original_programs[1]

        flipConstraintRewriter = FlipConstraintRewriter(f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}", False)
        parse_string(c.rules, lambda stm: (flipConstraintRewriter(stm)))
        weak_constraint = f":~not {SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}. [{SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"
        flipped_constraint = "\n".join(flipConstraintRewriter.program)
        flipped_constraint_with_weak = f"{flipped_constraint}\n{weak_constraint}"

        dummy_fact = f"{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}.\n:~{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}. [{SolverSettings.WEIGHT_FOR_DUMMY_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"

        self.rewritten_programs = [QuantifiedProgram(f"{self.original_programs[0].rules}\n{flipped_constraint_with_weak}\n{dummy_fact}",  self.original_programs[0].weak_constraints, ProgramQuantifier.FORALL, "", self.original_programs[0].head_predicates | self.original_programs[1].head_predicates | set([f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{c.name}"])), QuantifiedProgram("", [], ProgramQuantifier.CONSTRAINTS, "c", set())]
        self.update_programs()



    def rewrite_exists_weak_exists(self):
        # print("Rewriting an exists weak exists program")
        or_predicate_suffix = 0
        p_2 = self.original_programs[1]
        unsat_pred_name = f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{p_2.name}"
        rewriter_p_2 = OrProgramRewriter(set(), unsat_pred_name, False, p_2)
        rewriter_p_2.rewrite("", or_predicate_suffix)

        c = self.original_programs[1]
        rewriter_c = OrProgramRewriter(set(), unsat_pred_name, False, c)
        rewriter_c.rewrite("", or_predicate_suffix)

        unsat_choice = "{" + rewriter_p_2.unsat_atom_name + str(or_predicate_suffix) + "}."
        weak_repr = "\n".join([str(weak) for weak in self.original_programs[0].weak_constraints])
        rewritten_program = f"{self.original_programs[0].rules}{weak_repr}\n{rewriter_p_2.rewritten_program}\n{rewriter_c.rewritten_program}\n{unsat_choice}\n:~ {rewriter_p_2.unsat_atom_name}{or_predicate_suffix}.[{SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"
        
        #self.rewritten_programs = [QuantifiedProgram(rewritten_program, [], ProgramQuantifier.EXISTS, "p1", self.original_programs[0].head_predicates), QuantifiedProgram(rewriter_c.rewritten_program, [], ProgramQuantifier.CONSTRAINTS, "c", self.original_programs[2].head_predicates)]
        #the resulting ASPQ is an ASP program P_1 , which is equivalent to the ASPQ: \exists P_1 : C (with C = {})
        self.rewritten_programs = [QuantifiedProgram(rewritten_program, [], ProgramQuantifier.EXISTS, "p1", self.original_programs[0].head_predicates), QuantifiedProgram(rewritten_program, [], ProgramQuantifier.CONSTRAINTS, "c", set())]
        #P_1 = R(P_1) \cup R(P_2), but I am interested on models of P_1
        self.rewritten_programs[0].set_output_predicates(self.original_programs[0].head_predicates)
        self.update_programs()

    def rewrite_forall_weak_forall(self):
        # print("Rewriting a forall weak forall program")
        p_2 = self.original_programs[1]
        unsat_pred_name = f"{SolverSettings.UNSAT_PREDICATE_PREFIX}{p_2.name}"
        rewriter_p_2 = OrProgramRewriter(set(), unsat_pred_name, False, p_2)

        or_predicate_suffix = 0
        rewriter_p_2.rewrite("", or_predicate_suffix)

        programs_handler_rewriting = ProgramsHandler([QuantifiedProgram("", [], ProgramQuantifier.EXISTS, "", set()), self.original_programs[-1]], "", None)
        programs_handler_rewriting.flip_constraint()
        c = programs_handler_rewriting.neg_c()
        rewriter_c = OrProgramRewriter(set(), unsat_pred_name, False, c)
        rewriter_c.rewrite("", or_predicate_suffix)
        unsat_choice = "{" + rewriter_p_2.unsat_atom_name + str(or_predicate_suffix) + "}."
        weak_repr = "\n".join([str(weak) for weak in self.original_programs[0].weak_constraints])

        rewritten_program = f"{self.original_programs[0].rules}\n{weak_repr}\n{rewriter_p_2.rewritten_program}\n{rewriter_c.rewritten_program}\n{unsat_choice}\n:~ {rewriter_p_2.unsat_atom_name}{or_predicate_suffix}.[{SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS}@{SolverSettings.WEAK_NO_MODEL_LEVEL}]"

        # self.rewritten_programs = [QuantifiedProgram(rewritten_program, [], ProgramQuantifier.EXISTS, "p1", self.original_programs[0].head_predicates), QuantifiedProgram(rewriter_c.rewritten_program, [], ProgramQuantifier.CONSTRAINTS, "c", self.original_programs[2].head_predicates)]
        self.rewritten_programs = [QuantifiedProgram(rewritten_program, [], ProgramQuantifier.FORALL, "p1", self.original_programs[0].head_predicates), QuantifiedProgram("", [], ProgramQuantifier.CONSTRAINTS, "c", set())]
        #P_1 = R(P_1) \cup R(P_2), but I am interested on models of P_1
        self.rewritten_programs[0].set_output_predicates(self.original_programs[0].head_predicates)
        
        self.update_programs()


    def rewrite_exists_exists_weak(self):
        # print("Rewriting an exists exists weak program")
        #P1 takes rules of P_2 and a forall is added over the close 
        p_1 = self.original_programs[0]
        p_2 = self.original_programs[1]
        c = self.original_programs[2]

        check_rewriter = CheckRewriter(p_2, True, True)
        check_rewriter.rewrite(True, p_2.name)

        cloned_p2_program = check_rewriter.clone_program_rewriter.rewritten_program
        cloned_p2_program_head_predicates = check_rewriter.clone_program_rewriter.rewritten_program_head_predicates

        cost_p2_program = check_rewriter.cost_rewriter.rewritten_program
        cost_p2_head_predicates = check_rewriter.cost_rewriter.rewritten_program_head_predicates

        cost_clone_p2_program = check_rewriter.clone_cost_rewriter.rewritten_program
        cost_clone_p2_head_predicates = check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates

        dominated_program = check_rewriter.dominated_program
        dominated_program_head_predicates = check_rewriter.dominated_program_head_predicates
        
        c_program = f"{c.rules}\n{cost_p2_program}\n{cost_clone_p2_program}\n{dominated_program}\n:-{check_rewriter.dominated_predicate_name}."
        c_head_predicates = cost_p2_head_predicates | cost_clone_p2_head_predicates | dominated_program_head_predicates
        
        weak_repr = "\n".join([str(weak) for weak in p_1.weak_constraints])
        #p_1.weak_constraints are added since this method is also used when rewriting \forall_weak \forall_weak (after bumping up weak levels)
        self.rewritten_programs = [QuantifiedProgram(p_1.rules + "\n" + p_2.rules + "\n" + weak_repr, [], ProgramQuantifier.EXISTS, "p1", self.original_programs[0].head_predicates | self.original_programs[1].head_predicates), QuantifiedProgram(cloned_p2_program, [], ProgramQuantifier.FORALL, "p2", cloned_p2_program_head_predicates), QuantifiedProgram(c_program, [], ProgramQuantifier.CONSTRAINTS, "c", c_head_predicates)]
        
        #P_1 = P_1 \cup{{unsat}.}  \cup or(P_2, unsat) \cup or(C, unsat) \cup {:~unsat. [2@l_min]}, but I am interested on models of P_1
        self.rewritten_programs[0].set_output_predicates(self.original_programs[0].head_predicates)
        self.update_programs()

    def rewrite_forall_forall_weak(self):
        # print("Rewriting a forall forall weak program")
        p_1 = self.original_programs[0]
        p_2 = self.original_programs[1]
        c = self.original_programs[2]

        check_rewriter = CheckRewriter(p_2, True, True)
        check_rewriter.rewrite(True, p_2.name)

        cloned_p2_program = check_rewriter.clone_program_rewriter.rewritten_program
        cloned_p2_program_head_predicates = check_rewriter.clone_program_rewriter.rewritten_program_head_predicates

        cost_p2_program = check_rewriter.cost_rewriter.rewritten_program
        cost_p2_head_predicates = check_rewriter.cost_rewriter.rewritten_program_head_predicates

        cost_clone_p2_program = check_rewriter.clone_cost_rewriter.rewritten_program
        cost_clone_p2_head_predicates = check_rewriter.clone_cost_rewriter.rewritten_program_head_predicates

        dominated_program = check_rewriter.dominated_program
        dominated_program_head_predicates = check_rewriter.dominated_program_head_predicates
        
        or_c_rewriter = OrProgramRewriter(set(), check_rewriter.dominated_predicate_name, False, c_program)
        or_c_rewriter.rewrite("", -1)

        c_program = f"{or_c_rewriter.rewritten_program}\n{cost_p2_program}\n{cost_clone_p2_program}\n{dominated_program}"
        c_head_predicates = cost_p2_head_predicates | cost_clone_p2_head_predicates | dominated_program_head_predicates

        weak_repr = "\n".join([str(weak) for weak in p_1.weak_constraints])
        #p_1.weak_constraints are added since this method is also used when rewriting \exists_weak \exists_weak (after bumping up weak levels)
        self.rewritten_programs = [QuantifiedProgram(p_1.rules + "\n" + p_2.rules + "\n" + weak_repr, [], ProgramQuantifier.FORALL, "p1", self.original_programs[0].head_predicates | self.original_programs[1].head_predicates), QuantifiedProgram(cloned_p2_program, [], ProgramQuantifier.EXISTS, "p2", cloned_p2_program_head_predicates), QuantifiedProgram(c_program, [], ProgramQuantifier.CONSTRAINTS, "c", c_head_predicates)]
        #P_1 = P_1 \cup{{unsat}.}  \cup or(P_2, unsat) \cup or(neg(C), unsat) \cup {:~unsat. [2@l_min]}, but I am interested on models of P_1
        self.rewritten_programs[0].set_output_predicates(self.original_programs[0].head_predicates)
        self.update_programs()

    def update_programs(self):
        if len(self.rewritten_programs) != 0:
            self.rewritten_program_contains_weak = False
            for program in self.rewritten_programs:
                if program.contains_weak():
                    self.rewritten_program_contains_weak = True
            self.original_programs = self.rewritten_programs
            self.rewritten_programs = []

    def rewritten_program(self):
        if len(self.rewritten_programs) == 0:
            return self.original_programs
        return self.rewritten_programs
