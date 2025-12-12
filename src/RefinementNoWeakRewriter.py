from .ReductRewriter import ReductRewriter
from .OrProgramRewriter import OrProgramRewriter
from .QuantifiedProgram import QuantifiedProgram, ProgramQuantifier
from .RefinementRewriter import RefinementRewriter


#Takes P_2, ..., P_n : C as programs
#flips quantifiers and constraint if the first program is \forall (i.e. the outermost program was a \exists)
#the first two programs collapse into a single ASP program
class RefinementNoWeakRewriter(RefinementRewriter):
    SUFFIX_P : str = "_p_"
    SUFFIX_N : str = "_n_"
    FAIL_ATOM_NAME = "fail_"

    reduct_rewriter : ReductRewriter
    original_programs_list : list
    rewritten_programs_list : list
    constraint_program_rewriter : OrProgramRewriter
    to_rewrite_constraint : QuantifiedProgram

    def __init__(self, original_programs, program_c, program_neg_c, ground_transformation):
        self.original_programs_list = original_programs
        self.reduct_rewriter = ReductRewriter(self.original_programs_list, self.SUFFIX_P, self.SUFFIX_N, self.FAIL_ATOM_NAME, ground_transformation)
        #Here given a program of the form \exists P_1 \forall P_2, ... \exists P_n : C I am getting \forall P_2, ... \exists P_n : C 
        self.to_rewrite_constraint = program_c if self.original_programs_list[0].program_type == ProgramQuantifier.FORALL else program_neg_c
        self.rewritten_programs_list = []
        self.constraint_program_rewriter = OrProgramRewriter(self.reduct_rewriter.to_rewrite_predicates, self.FAIL_ATOM_NAME, True, self.to_rewrite_constraint)

    def rewrite(self, counterexample, iteration):
        self.reduct_rewriter.rewrite(counterexample, iteration)
    
        self.constraint_program_rewriter.rewrite(self.SUFFIX_P, iteration)
        self.rewritten_programs_list = [*self.reduct_rewriter.rewritten_programs_list, QuantifiedProgram(self.constraint_program_rewriter.rewritten_program, [], ProgramQuantifier.CONSTRAINTS, "c", self.to_rewrite_constraint.head_predicates)]
        
        
    #called from outside only when the refinement becomes an ASP program
    def refined_program(self):
        #collapse the first three programs into an exists program and rename the remaining ones
        if len(self.original_programs_list) > 3:
            refinement_aspq = []
            refinement_str = ""
            head_predicates = set()

            for i in range(2):
                refinement_str += self.rewritten_programs_list[i].rules
                head_predicates = head_predicates | self.rewritten_programs_list[i].head_predicates

            refinement_aspq.append(QuantifiedProgram(refinement_str, [], ProgramQuantifier.EXISTS, "1", head_predicates))
            
            for i in range(2, len(self.rewritten_programs_list)):
                #the third program has name 4 since 1 is not in the original list
                self.rewritten_programs_list[i].name = str(i-3)
                refinement_aspq.append(self.rewritten_programs_list[i])
            return refinement_aspq
        else:#refinement is a single exists program and just the textual representation in enough - no need to build an ASPQ solver for it
            refinement_str = ""
            #collapse the first three quantifiers into an exists quantifier and leave the rest of the program unchanged
            for program in self.rewritten_programs_list:
                refinement_str += program.rules
            #refinement_str += self.counterexample_facts
            return refinement_str

    def compute_placeholder_program(self):
        self.constraint_program_rewriter.compute_placeholder_program()
        self.reduct_rewriter.compute_placeholder_program()