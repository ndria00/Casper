from .DebugLogger import DebugLogger
from .ExecutionLogger import ExecutionLogger
from .MyLogger import MyLogger


class SolverSettings:

    DUMMY_WEAK_PREDICATE_NAME : str = "dummy"
    DOMINATED_ATOM_NAME : str = "dominated"
    CLONE_ATOM_SUFFIX : str = "_clone"
    COST_AT_LEVEL_ATOM_NAME : str = "cost_at_level"
    WEAK_VIOLATION_ATOM_NAME : str = "violated"
    DIFF_COST_AT_LEVEL : str = "diff"
    HAS_HIGHER_DIFF : str = "hasHigher"
    HIGHEST_LEVEL_DIFF : str = "highest"
    LEVEL_COST_ATOM_NAME : str = "level"
    UNSAT_PREDICATE_PREFIX : str = "unsat_p"
    ACTIVATE_CLONE_PREDICATE : str = "activate"
    EXTERNAL_PREDICATE_FOR_ACTIVATE_CONSTRAINT : str = "external"
    FLAG_ATOM_NAME : str = "flag_"
    DUMMY_REFINEMENT_PREDICATE = "dummy_ref"
    RELAXED_CPREDICATE : str = "violated_constraint"
    UNSAT_C_PREDICATE : str = "unsat_c"

    n_models : int
    debug : bool
    constraint_print : bool
    enumeration : bool
    logger : MyLogger
    ground_transformation : bool
    no_weak : bool

    def __init__(self, n_models, debug, constraint_print, ground_transformation, no_weak):
        self.ground_transformation = ground_transformation
        self.n_models = n_models
        self.debug = debug
        self.constraint_print = constraint_print
        self.no_weak = no_weak
        self.enumeration = True if n_models == 0 else False
        if debug:
            self.logger = DebugLogger()
        else:
            self.logger = ExecutionLogger()
