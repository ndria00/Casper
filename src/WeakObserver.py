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
        
