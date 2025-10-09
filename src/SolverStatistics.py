class SolverStatistics:
    _instance = None
    conterexample_found : int = 0
    aspq_solvers_calls : int = 0
    models_found : int = 0
    solvers_iterations : int = 0
    
    def __new__(cls, *args, **kwargs):
        if cls._instance is None:
            cls._instance = super(SolverStatistics, cls).__new__(cls)
        return cls._instance

    def __init__(self):
        pass

    def model_found(self):
        self._instance.models_found += 1

    def iteration_done(self):
        self.solvers_iterations +=1

    def print_statistics(self):
        print(f"Models found {self._instance.models_found}")
        print(f"ASPQ solvers calls {self._instance.aspq_solvers_calls}")
        print(f"Counterexample found {self._instance.conterexample_found}")