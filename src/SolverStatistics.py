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

    def counterexample_found(self):
        self.conterexample_found+=1

    def model_found(self):
        self.models_found += 1

    def iteration_done(self):
        self.solvers_iterations +=1

    def print_statistics(self):
        print(f"Models found {self.models_found}")
        print(f"ASPQ solvers calls {self.solvers_iterations}")
        print(f"Counterexample found {self.conterexample_found}")

