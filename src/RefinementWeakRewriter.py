
import clingo
from clingo.ast import parse_string

from .SolverSettings import SolverSettings
from .OrUnsatWeakRewriter import OrUnsatWeakRewriter
from .ReductRewriter import ReductRewriter
from .CloneRewriter import CloneRewriter
from .QuantifiedProgram import ProgramQuantifier
from .OrProgramRewriter import OrProgramRewriter
from .CheckRewriter import CheckRewriter
from .RefinementRewriter import RefinementRewriter
from .CostRewriter import CostRewriter
from .QuantifiedProgram import QuantifiedProgram

class RefinementWeakRewriter(RefinementRewriter):
    original_programs_list : list
    rewritten_program : str
    check_rewriter : CheckRewriter
    counterexample_cost_rewriter : CostRewriter
    external_predicates : list
    refinements_fail_predicates : list 
    num_calls : int

    def __init__(self, original_programs_list, program_c, program_neg_c, ground_transformation):
        assert(len(original_programs_list) == 1)
        self.original_programs_list = original_programs_list
        self.ground_transformation = ground_transformation
        self.rewritten_program = ""
        self.num_calls = 0
        self.external_predicates = []
        self.refinements_fail_predicates = []
        self.reduct_rewriter = ReductRewriter([self.original_programs_list[0]], self.SUFFIX_P, self.SUFFIX_N, self.FAIL_ATOM_NAME, ground_transformation)
        self.constraint_program_rewriter = OrUnsatWeakRewriter(self.reduct_rewriter.to_rewrite_predicates, self.FAIL_ATOM_NAME, SolverSettings.RELAXED_CPREDICATE, -3, True, program_neg_c if self.original_programs_list[-1].program_type == ProgramQuantifier.EXISTS else program_c)
        
        self.check_rewriter = CheckRewriter(self.original_programs_list[0])
        
    def compute_placeholder_program(self):
        self.reduct_rewriter.compute_placeholder_program()

    def rewrite(self, counterexample, iteration):

        self.rewritten_program = ""

        #reduct(P_2, M_2)
        self.reduct_rewriter.rewrite(counterexample, iteration)
        self.refinements_fail_predicates.append(self.reduct_rewriter.current_fail_predicate)
        
        #or(P_C, fail_{iteration})
        self.constraint_program_rewriter.rewrite(self.SUFFIX_P, iteration)

        self.relaxed_or_constraint_program = self.constraint_program_rewriter.rewritten_program

        #cost(P_2) over p_{iteration} signature. cost of clone of P_2 
        self.check_rewriter.rewrite(False if self.num_calls > 0 else True, f"{self.SUFFIX_P}{str(iteration)}") 
        
        #compute or with clone and cost of clone just once - these two programs are the same across refinements
        if self.num_calls == 0:
            or_clone_program_rewriter = OrProgramRewriter(set(), SolverSettings.ACTIVATE_CLONE_PREDICATE, False, QuantifiedProgram(self.check_rewriter.clone_program, [], ProgramQuantifier.EXISTS, "", set()), False)
            or_clone_cost_program_rewriter = OrProgramRewriter(set(), SolverSettings.ACTIVATE_CLONE_PREDICATE, False, QuantifiedProgram(self.check_rewriter.clone_cost_program, [], ProgramQuantifier.EXISTS, "", set()), False)
            or_clone_program_rewriter.rewrite("", None)
            or_clone_cost_program_rewriter.rewrite("", None)
            activated_clone_program = or_clone_program_rewriter.rewritten_program
            activated_clone_cost_program = or_clone_cost_program_rewriter.rewritten_program
            self.activate_choice = "{" + SolverSettings.ACTIVATE_CLONE_PREDICATE + "}."
            #used for forcing clingo to report a cost for all levels (even those that have no violation tuples) 
            dummy_weak_rules_and_fact = f"{SolverSettings.DUMMY_REFINEMENT_PREDICATE}.\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-1}]\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-2}]\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-3}]"
            self.rewritten_program = f"{self.activate_choice}\n{activated_clone_program}\n{activated_clone_cost_program}\n{dummy_weak_rules_and_fact}"
        
        self.external_predicates.append(f"{SolverSettings.FLAG_ATOM_NAME}{iteration}")
        fail_predicates = ", ".join(self.refinements_fail_predicates)
        not_activate_if_no_answer_constraint = f":-{SolverSettings.ACTIVATE_CLONE_PREDICATE}, {fail_predicates}, {str(self.external_predicates[-1])}."
        not_activate_not_fail_constraint = f":-not {SolverSettings.ACTIVATE_CLONE_PREDICATE}, not {self.reduct_rewriter.current_fail_predicate}.\n"
        refinement_weak_constraints = f":~not {self.reduct_rewriter.current_fail_predicate}.[1@{QuantifiedProgram.MIN_WEAK_LEVEL-1}]\n:~not {self.reduct_rewriter.current_fail_predicate}, not {self.check_rewriter.dominated_predicate_name}.[1@{QuantifiedProgram.MIN_WEAK_LEVEL-2}]\n:~not {self.reduct_rewriter.current_fail_predicate}, {SolverSettings.RELAXED_CPREDICATE}{self.SUFFIX_P}{iteration}.[1@{QuantifiedProgram.MIN_WEAK_LEVEL-3}]"
        joined_programs_rules = "\n".join(program.rules for program in self.reduct_rewriter.rewritten_programs_list)
        self.rewritten_program = f"{self.rewritten_program}\n{joined_programs_rules}\n{self.relaxed_or_constraint_program}\n{self.check_rewriter.cost_program}\n{self.check_rewriter.dominated_program}\n{refinement_weak_constraints}\n{not_activate_if_no_answer_constraint}\n{not_activate_not_fail_constraint}\n"
        self.num_calls += 1

    def dummy_refinement_weaks(self):
        return f"{SolverSettings.DUMMY_REFINEMENT_PREDICATE}.\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-1}]\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-2}]\n:~{SolverSettings.DUMMY_REFINEMENT_PREDICATE}. [0@{QuantifiedProgram.MIN_WEAK_LEVEL-3}]"


    def refined_program(self):
        return self.rewritten_program
