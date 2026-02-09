import logging
from .QuantifiedProgram import QuantifiedProgram

class SolverSettings:

    DOMINATED_ATOM_NAME : str = "dominated"
    CLONE_ATOM_SUFFIX : str = "_clone"
    COST_AT_LEVEL_ATOM_NAME : str = "cost_at_level"
    GLOBAL_WEAK_COST_AT_LEVEL_ATOM_NAME: str = "cost_at_level_global"
    WEAK_VIOLATION_ATOM_NAME : str = "violated"
    GLOBAL_WEAK_VIOLATION_ATOM_NAME : str = "violated_global"
    GLOBAL_WEAK_VIOLATED_BOUND_ATOM_NAME: str = "violated_global_bound"
    DIFF_COST_AT_LEVEL : str = "diff"
    HAS_HIGHER_DIFF : str = "hasHigher"
    HIGHEST_LEVEL_DIFF : str = "highest"
    LEVEL_COST_ATOM_NAME : str = "level"
    UNSAT_PREDICATE_PREFIX : str = "unsat_p"
    ACTIVATE_CLONE_PREDICATE : str = "activate"
    EXTERNAL_PREDICATE_FOR_ACTIVATE_CONSTRAINT : str = "external"
    EXTERNAL_PREDICATE_FOR_ACTIVATE_COST_CONSTRAINT : str = "external_cost"
    FLAG_ATOM_NAME : str = "flag_"
    RELAXED_CPREDICATE : str = "violated_constraint"
    UNSAT_C_PREDICATE : str = "unsat_c"
    FOUND_LEVEL : str = "found_level"

    WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS: int = 1

    WEAK_NO_MODEL_LEVEL : int = QuantifiedProgram.MIN_WEAK_LEVEL -1
    WEAK_NOT_DOMINATED_LEVEL : int = QuantifiedProgram.MIN_WEAK_LEVEL -2
    WEAK_CONSTRAINT_LEVEL : int = QuantifiedProgram.MIN_WEAK_LEVEL -3
    GLOBAL_WEAK_CONSTRAINT_LEVEL: int = QuantifiedProgram.MIN_WEAK_LEVEL -4

    n_models : int
    debug : bool
    constraint_print : bool
    enumeration : bool
    logger : logging.Logger
    ground_transformation : bool
    no_weak : bool
    collapse_global_weak : bool
    json_format : bool

    def __init__(self, n_models, debug, constraint_print, ground_transformation, no_weak, collapse_global_weak=False, json_format=False):
        self.ground_transformation = ground_transformation
        self.n_models = n_models
        self.debug = debug
        self.constraint_print = constraint_print
        self.no_weak = no_weak
        self.enumeration = True if n_models == 0 else False
        self.setup_logging(self.debug)
        self.collapse_global_weak = collapse_global_weak
        self.json_format = json_format

    def setup_logging(self, debug: bool):
        logging.basicConfig()
        self.logger = logging.getLogger("Casper")
        level = logging.DEBUG if debug else logging.INFO
        self.logger.setLevel(level)