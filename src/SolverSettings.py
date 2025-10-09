from .DebugLogger import DebugLogger
from .ExecutionLogger import ExecutionLogger
from .MyLogger import MyLogger


class SolverSettings:

    n_models : int
    debug : bool
    constraint_print : bool
    enumeration : bool
    logger : MyLogger
    ground_transformation : bool

    def __init__(self, n_models, debug, constraint_print, ground_transformation):
        self.ground_transformation = ground_transformation
        self.n_models = n_models
        self.debug = debug
        self.constraint_print = constraint_print
        self.enumeration = True if n_models == 0 else False
        if debug:
            self.logger = DebugLogger()
        else:
            self.logger = ExecutionLogger()
