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
from .ModelPrinter import ModelPrinter


class ConstraintModelPrinter(ModelPrinter):
    
    def __init__(self):
        pass
    
    def print_model(self, model, p1_symbols):
        print("Model:{", end="")

        for symbol in p1_symbols:
            if symbol in model:
                print(":- not ", symbol, ". ",end="")
            else:
                print(":- ", symbol, ". ",end="")
        print("}")