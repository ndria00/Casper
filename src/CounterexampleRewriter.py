from .QuantifiedProgram import QuantifiedProgram, ProgramQuantifier

#Takes P_2, ..., P_n : C as programs
#flips quantifiers and constraint if the first program is \exists (i.e. the outermost program was a \forall)
class CounterexampleRewriter:
    constraint_program : QuantifiedProgram
    negated_constraint_program : QuantifiedProgram
    original_programs_list : list
    rewritten_programs_list : list
    flip_quantifier_and_constraint: bool
    first_rewrite : bool
    first_program_rewritten : str

    def __init__(self, original_programs, program_c, program_neg_c):
        self.original_programs_list = original_programs
        self.constraint_program = program_c
        self.negated_constraint_program = program_neg_c
        self.rewritten_programs_list = []
        
        #flip constraint if the first program to rewrite is a forall (e.g, the first program of the ASPQ is quantified existentially) 
        self.flip_quantifier_and_constraint = True if self.original_programs_list[0].program_type == ProgramQuantifier.FORALL else False 
        if self.flip_quantifier_and_constraint:
            self.original_programs_list.append(program_neg_c)
        else:
            self.original_programs_list.append(program_c)
        self.first_rewrite = True

    def rewritten_program(self):
        return self.rewritten_programs_list


    def rewrite(self, model, p1_symbols, p1_predicates):
        #on the first call construct counterexample program
        #on subsequent calls the counterexample program can be reused
        #but the assumptions have to be updated
        if self.first_rewrite:
            self.rewritten_programs_list = []
            for i in range(len(self.original_programs_list)-1):
                quantifier = None
                if self.flip_quantifier_and_constraint:
                    quantifier = ProgramQuantifier.EXISTS  if self.original_programs_list[i].program_type == ProgramQuantifier.FORALL else ProgramQuantifier.FORALL
                else:
                    quantifier = self.original_programs_list[i].program_type
                prg = self.original_programs_list[i]
                self.rewritten_programs_list.append(QuantifiedProgram(prg.rules, [], quantifier, prg.name, prg.head_predicates))        
            if self.flip_quantifier_and_constraint:
                self.rewritten_programs_list.append(self.negated_constraint_program)
            else:
                self.rewritten_programs_list.append(self.constraint_program)
            self.first_program_rewritten = self.rewritten_programs_list[0].rules
        
        assumptions = []
        for symbol in p1_symbols:
            if symbol in model and symbol.name in p1_predicates:
                assumptions.append(f"{symbol}.")
            # else:
            #     assumptions.append(f"not {symbol}.")
        self.rewritten_programs_list[0].rules = self.first_program_rewritten + " ".join(assumptions)