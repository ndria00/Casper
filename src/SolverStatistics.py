# Copyright [2025] [Andrea Cuteri, Giuseppe Mazzotta and Francesco Ricca]

#    Licensed under the Apache License, Version 2.0 (the "License");
#    you may not use this file except in compliance with the License.
#    You may obtain a copy of the License at

#        http://www.apache.org/licenses/LICENSE-2.0

#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#    See the License for the specific language governing permissions and
#    limitations under the License.
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

