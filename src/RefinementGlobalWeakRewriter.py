from .CostRewriter import CostRewriter
from .SolverSettings import SolverSettings
from .QuantifiedProgram import QuantifiedProgram

class RefinementGlobalWeakRewriter:

    cost_rewriter : CostRewriter
    weak_program : QuantifiedProgram
    rewritten_program : str
    cost_bound : int
    rewriting_iteration : int
    placeholder_constraint : str
    violated_bound_atoms : str
    sorted_levels : list
    global_weak_violation_atoms_for_level : dict
    total_cost_for_level : dict
    #external atoms used for activating only the last constraint (used for enumeration of optimal models) 
    # external_atoms : list
    iteration : int
    current_violated_bound_atom_name : str

    def __init__(self, weak_program):
        self.weak_program = weak_program
        self.cost_rewriter = CostRewriter(weak_program, SolverSettings.GLOBAL_WEAK_VIOLATION_ATOM_NAME, SolverSettings.GLOBAL_WEAK_VIOLATION_ATOM_NAME, SolverSettings.GLOBAL_WEAK_COST_AT_LEVEL_ATOM_NAME, False, True)
        self.rewritten_program = ""
        self.cost_bound = 0
        # self.external_atoms = []
        self.placeholder_constraint = ""
        self.rewriting_iteration = 0
        self.sorted_levels = []
        self.global_weak_violation_atoms_for_level = dict()
        self.total_cost_for_level = dict()
        self.iteration = 0
        self.violated_bound_atoms = []
        self.current_violated_bound_atom_name  = ""

    def compute_placeholder_program(self, symbolic_atoms):
        for atom in symbolic_atoms:
            if atom.symbol.name == SolverSettings.GLOBAL_WEAK_VIOLATION_ATOM_NAME:
                weight, level = [int(str(n)) for n in atom.symbol.arguments[:2]]
                negated = weight < 0
                if level in self.global_weak_violation_atoms_for_level:
                    self.global_weak_violation_atoms_for_level[level].append((atom.symbol, negated))
                else:
                    self.global_weak_violation_atoms_for_level[level] = [(atom.symbol, negated)]
        prev_sum = 1
        levels = sorted([lev for lev in self.global_weak_violation_atoms_for_level])
        ground_set = []
        for lev in levels:
            current_cost = 1
            for (symbol,negated) in self.global_weak_violation_atoms_for_level[lev]:
                tuple_weight = int(str(symbol.arguments[0]))
                tuple_weight = tuple_weight if tuple_weight >= 0 else -tuple_weight
                weight = prev_sum * tuple_weight 
                current_cost += weight
                tuple_ = str(weight) if len(symbol.arguments) == 1 else ",".join([str(weight)]+[str(n) for n in symbol.arguments[1:]])
                naf = "" if not negated else "not "
                ground_set.append(f"{tuple_}:{naf}{str(symbol)}")
            prev_sum += current_cost
            self.total_cost_for_level[lev] = prev_sum

        template_constraint = "; ".join(ground_set)
        
        self.placeholder_constraint = "[[V_global_head]]" + ":- #sum{" + template_constraint +"} >= [[bound]].\n:~ [[V_global_head]]. [" + str(SolverSettings.WEIGHT_FOR_VIOLATED_WEAK_CONSTRAINTS) + "@" + str(SolverSettings.GLOBAL_WEAK_CONSTRAINT_LEVEL) + "]"
        self.sorted_levels = sorted([level for level in self.global_weak_violation_atoms_for_level])
        
    def compute_cost_and_new_upper_bound(self, model=None):
        assert self.placeholder_constraint != ""
        prev_sum = 1
        bound = 0
        cost_string = ""
        self.current_violated_bound_atom_name = f"{SolverSettings.GLOBAL_WEAK_VIOLATED_BOUND_ATOM_NAME}{self.iteration}"
        self.violated_bound_atoms.append(self.current_violated_bound_atom_name)
        for lev in self.sorted_levels:
            current_cost = 0
            for (atom,negated) in self.global_weak_violation_atoms_for_level[lev]:
                weight = int(str(atom.arguments[0]))
                pos_weight = weight if weight >= 0 else -weight
                if atom in model:
                    current_cost += weight
                if (negated and atom in model) or (not negated and atom not in model):
                    continue
                bound += prev_sum * pos_weight
            cost_string = cost_string + str(lev) + ":" + str(current_cost) + (", " if lev != self.sorted_levels[-1] else "" )   
            # print(lev,":",current_cost,end=", " if lev != self.sorted_levels[-1] else "")
            prev_sum = self.total_cost_for_level[lev]
        # print()
        self.iteration += 1
        return (self.placeholder_constraint.replace("[[bound]]",str(bound)).replace("[[V_global_head]]", self.current_violated_bound_atom_name), cost_string)    
