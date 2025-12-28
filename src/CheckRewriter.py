
from .SolverSettings import SolverSettings
from .CloneRewriter import CloneRewriter
from .CostRewriter import CostRewriter
from .QuantifiedProgram import QuantifiedProgram


class CheckRewriter:
    program : QuantifiedProgram
    cost_program : str

    dominated_program : str
    dominated_program_head_predicates : set
    
    cost_rewriter : CostRewriter
    clone_program_rewriter : CloneRewriter
    clone_program : str 
    clone_cost_rewriter : CloneRewriter
    clone_cost_program : str
    dominated_predicate_name : str
    rewriting_program_name : str
    rewrite_level_predicate : bool

    def __init__(self, program, keep_body_signature_for_cost = True, rewrite_level_predicate=True, rewrite_for_missing_level=False):
        self.program = program
        self.keep_body_signature_for_cost = keep_body_signature_for_cost
        self.cost_rewriter = CostRewriter(self.program, SolverSettings.WEAK_VIOLATION_ATOM_NAME, SolverSettings.LEVEL_COST_ATOM_NAME, SolverSettings.COST_AT_LEVEL_ATOM_NAME, self.keep_body_signature_for_cost, rewrite_level_predicate)
        self.clone_program = ""
        self.dominated_program = ""
        self.dominated_program_head_predicates = set()
        self.clone_cost_program = ""
        self.dominated_predicate_name = ""
        self.rewrite_level_predicate = rewrite_level_predicate
        self.rewrite_for_missing_level = rewrite_for_missing_level

    def rewrite(self, create_clone=True, suffix=""):
        self.dominated_predicate_name = f"{SolverSettings.DOMINATED_ATOM_NAME}{suffix}"
        self.dominated_program = ""
        self.dominated_program_head_predicates = set()
        #cost program from self.prorgam -> weak become normals
        self.cost_rewriter.rewrite(suffix)
        self.cost_program = self.cost_rewriter.rewritten_program_with_aggregate_and_levels()
        #clone of program is needed only by weak rewriters
        if create_clone:
            self.rewriting_program_name = suffix
            self.clone_program_rewriter = CloneRewriter(self.program, f"{suffix}{SolverSettings.CLONE_ATOM_SUFFIX}", set([SolverSettings.LEVEL_COST_ATOM_NAME]) if not self.rewrite_level_predicate else set())
            #clone program from self.program -> predicates are rewritten to the clone signature
            self.clone_program_rewriter.rewrite()
            self.clone_program = self.clone_program_rewriter.rewritten_program
            #clone of cost program -> predicates are rewritten to the clone signature 
            self.cost_rewriter.rewrite()
            cost_program_no_suffix = self.cost_rewriter.rewritten_program_with_aggregate_and_levels()
            #I should rewrite to the clone signature both predicates from cost program and from the original program
            self.clone_cost_rewriter = CloneRewriter(QuantifiedProgram(cost_program_no_suffix, [], self.program.program_type, "", self.program.head_predicates | self.cost_rewriter.rewritten_program_head_predicates_with_levels_and_aggregate), f"{suffix}{SolverSettings.CLONE_ATOM_SUFFIX}", set([SolverSettings.LEVEL_COST_ATOM_NAME]) if not self.rewrite_level_predicate else set())
            self.clone_cost_rewriter.rewrite()
            self.clone_cost_program = self.clone_cost_rewriter.rewritten_program
        self.construct_dominated_program(suffix)

    def construct_dominated_program(self, suffix):
        diff_rule = f"{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L):-{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{suffix}(C1,L), {SolverSettings.COST_AT_LEVEL_ATOM_NAME}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(C2,L),C1!=C2."
        diff_rules_no_level = ""
        if self.rewrite_for_missing_level:
            found_level_rule = f"{SolverSettings.FOUND_LEVEL}{suffix}(L):-{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{suffix}(C,L)."
            found_level_rule_clone = f"{SolverSettings.FOUND_LEVEL}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(L):-{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(C,L)."
            diff_rule_no_level_in_clone = f"{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L):-{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{suffix}(C1,L), C1!=0, not {SolverSettings.FOUND_LEVEL}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(L)."
            diff_rule_no_level = f"{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L):-{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(C1,L), C1!=0, not {SolverSettings.FOUND_LEVEL}{suffix}(L)."
            diff_rules_no_level = f"{found_level_rule}\n{found_level_rule_clone}\n{diff_rule_no_level_in_clone}\n{diff_rule_no_level}"

        has_higher_rule = f"{SolverSettings.HAS_HIGHER_DIFF}{suffix}(L):-{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L), {SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L1), L<L1."
        highest_rule = f"{SolverSettings.HIGHEST_LEVEL_DIFF}{suffix}(L):-{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}(L), not {SolverSettings.HAS_HIGHER_DIFF}{suffix}(L)."
        dominated_rule = f"{self.dominated_predicate_name}:-{SolverSettings.HIGHEST_LEVEL_DIFF}{suffix}(L),{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{suffix}(C1,L),{SolverSettings.COST_AT_LEVEL_ATOM_NAME}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}(C2,L),C2<C1."
        
        self.dominated_program = f"{diff_rule}\n{has_higher_rule}\n{highest_rule}\n{dominated_rule}\n"
        self.dominated_program_head_predicates ={f"{SolverSettings.DIFF_COST_AT_LEVEL}{suffix}", f"{SolverSettings.HAS_HIGHER_DIFF}{suffix}", f"{SolverSettings.HIGHEST_LEVEL_DIFF}{suffix}", f"{self.dominated_predicate_name}"}
        if self.rewrite_for_missing_level:
            self.dominated_program_head_predicates = set([self.dominated_predicate_name]) | set([f"{SolverSettings.FOUND_LEVEL}{suffix}", f"{SolverSettings.FOUND_LEVEL}{self.rewriting_program_name}{SolverSettings.CLONE_ATOM_SUFFIX}"])
            self.dominated_program = f"{self.dominated_program}\n{diff_rules_no_level}"
