from .ModelPrinter import ModelPrinter

class ASPChefModelPrinter(ModelPrinter):
    def __init__(self):
        pass

    def print_model(self, model, p1_symbols):
        model_symbols_set = set()
        for symbol in model:
            model_symbols_set.add(symbol)

        print("{\"literals\" : [", end="")
        out_symbols = []
        for symbol in p1_symbols:
            if symbol in model_symbols_set:
                out_symbols.append(f"\"{symbol}\"")
            else:
                out_symbols.append(f"\"not {symbol}\"")
        print(", ".join(out_symbols), end = "")
        print("]}")