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

    def pay_dummy_program(self):
        dummy_weak_rules = []

        for weak in self.weak_levels:
            if weak > 0:
                dummy_weak_rules.append(f":~{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}. [0@{weak}]")
            else:#negative levels are reserverd for detecting violation of c(resp.  neg c)
                dummy_weak_rules.append(f":~{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}. [{SolverSettings.WEIGHT_FOR_DUMMY_CONSTRAINTS}@{weak}]")
        dummy_fact = "" 
        if len(self.weak_levels) > 0:
            dummy_fact = f"{SolverSettings.DUMMY_WEAK_PREDICATE_NAME}."

        return "\n".join(dummy_weak_rules) + f"\n{dummy_fact}"
        
