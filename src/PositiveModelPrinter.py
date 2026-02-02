from .ModelPrinter import ModelPrinter

class PositiveModelPrinter(ModelPrinter):
    def __init__(self):
        pass

    def print_model(self, model, p1_symbols):
        print("Model:{", end="")
        for symbol in model:
            if symbol in p1_symbols:
                print(f"{symbol}.",end=" ")
        print("}")