from clingo.ast import parse_string
from .FlipConstraintRewriter import FlipConstraintRewriter
from .MyProgram import MyProgram, ProgramQuantifier
from .RelaxedRewriter import RelaxedRewriter
from .SplitProgramRewriter import SplitProgramRewriter


class ProgramsHandler:
    
    encoding : str
    original_programs_list : list
    relaxed_programs_list : list
    relaxed_rewriter : RelaxedRewriter
    split_rewriter : SplitProgramRewriter
    flipped_constraint : MyProgram
    
    def split_programs(self):
        self.split_rewriter = SplitProgramRewriter()
        parse_string(self.encoding, lambda stm: (self.split_rewriter(stm)))
        self.split_rewriter.check_aspq_type()
        for i in range(1,len(self.split_rewriter.programs)+1):
            prg = self.split_rewriter.programs[i-1]
            self.original_programs_list.append(prg)

    def relax_programs(self):
        lvl = len(self.split_rewriter.programs)
        for i in range(1,len(self.split_rewriter.programs)+1):
            prg = self.split_rewriter.programs[i-1]
            self.relaxed_rewriter = RelaxedRewriter(lvl, f"unsat_{prg.name}")
            parse_string("\n".join(prg.rules), lambda stm : (self.relaxed_rewriter(stm)))

            # print(f"Adding program to ctl: {self.relaxed_rewriter.program}")
            # self.ctl.add(prg.name, [], "\n".join(self.relaxed_rewriter.program))
            self.relaxed_programs_list.append(MyProgram(program_name=prg.name, program_type=prg.program_type, head_predicates=self.relaxed_rewriter.head_predicates, rules=self.relaxed_rewriter.program))
            #print("Original program was ", prg.rules)
            #print("Relaxed program is ", self.relaxed_programs[len(self.relaxed_programs)-1])
            # print(f"Added program with name {prg.name} -> {relaxed_rewriter.program} and type {prg.program_type}")
            self.relaxed_rewriter.reset()
            lvl -= 1
        
        # prg = self.split_rewriter.programs[len(self.split_rewriter.programs) -1]
        # constraint_rewriter = ConstraintRewriter(lvl, "unsat_c")
        # parse_string("\n".join(prg.rules), lambda stm : (constraint_rewriter(stm)))
        # self.relaxed_programs.append(MyProgram(program_name=prg.name, program_type=prg.program_type, head_predicates=constraint_rewriter.head_predicates, rules=constraint_rewriter.program))

    def flip_constraint(self):
        flipConstraintRewriter = FlipConstraintRewriter("unsat_c")
        constraint_program = self.original_programs_list[len(self.original_programs_list)-1]
        parse_string("\n".join(constraint_program.rules), lambda stm: (flipConstraintRewriter(stm)))
        self.flipped_constraint = MyProgram(rules=flipConstraintRewriter.program, program_type=ProgramQuantifier.CONSTRAINTS, program_name=constraint_program.name, head_predicates=flipConstraintRewriter.head_predicates) 

    def p(self, idx):
        if idx < 0 or idx >= len(self.original_programs_list):
            raise Exception("Incorrect program index")
        return self.original_programs_list[idx]
    
    def last_exists(self):
        #constrant in \Pi -> last program is at index -2
        if self.original_programs_list[len(self.original_programs_list)-1].program_type == ProgramQuantifier.CONSTRAINTS:
            return self.original_programs_list[len(self.original_programs_list)-2].program_type == ProgramQuantifier.EXISTS
        #no constrant in \Pi -> last program is at index -1
        return self.original_programs_list[len(self.original_programs_list)-1].program_type == ProgramQuantifier.EXISTS
    
    
    def c(self):
        return self.original_programs_list[len(self.original_programs_list)-1]

    def neg_c(self):
        return self.flipped_constraint

    def __init__(self, encoding, relax_programs):
        self.encoding = encoding
        self.original_programs_list = []
        self.relaxed_programs_list = []
        self.flipped_constraint = None
        self.split_programs()
        #add empty constraint program if no constraint program was parsed
        if self.original_programs_list[len(self.original_programs_list)-1].program_type != ProgramQuantifier.CONSTRAINTS:
            self.original_programs_list.append(MyProgram([], ProgramQuantifier.CONSTRAINTS, "c", set()))
        if relax_programs:
            self.relax_programs()
        self.flip_constraint()