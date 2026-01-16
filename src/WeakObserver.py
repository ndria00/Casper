from typing import List, Sequence, Tuple
import clingo

from .SolverSettings import SolverSettings


#used to construct weak constraints with dummy tuple that pay 0 at every weak level
class WeakObserver(clingo.Observer):
    weak_levels : set

    def __init__(self):
        self.weak_levels = set()

    def minimize(self, priority: int, literals: List[Tuple[int,int]]) -> None:
        #if I leave this check here I will catch negative levels from weak refinement
        # if priority < 0:
        #     raise Exception("Negative weak levels are not allowed")
        self.weak_levels.add(priority)
        
