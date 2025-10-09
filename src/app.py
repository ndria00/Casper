from clingo.ast import parse_string
from .SolverStatistics import SolverStatistics
from .SplitProgramRewriter import SplitProgramRewriter
from .ProgramsHandler import ProgramsHandler
from .SolverSettings import SolverSettings
from .ASPQSolver import ASPQSolver
import argparse

def entrypoint():
    parser = argparse.ArgumentParser(prog = "Casper", description = "A native solver based on CEGAR for 2-ASP(Q)\n")

    parser.add_argument('--problem', help="path to problem file\n", required=True)
    parser.add_argument('--instance', help="path to instance file\n", required=False, default="")
    parser.add_argument('--debug', help="enable debug\n", required=False, action="store_true")
    parser.add_argument('--statistics', help="print solving statistics\n", required=False, action="store_true")
    parser.add_argument('--constraint', help="enable constraint print of models\n", required=False, action="store_true")
    parser.add_argument('-n', help="number of q-answer sets to compute (if zero enumerate)\n", default=1)
    args = parser.parse_args()
    encoding_path = args.problem
    instance_path = args.instance
    
    #read encoding program and possibly also instance program
    encoding_program = ""
    instance_program = ""
    try:
        encoding_program = "\n".join(open(encoding_path).readlines())
    except:
        print("Could not open problem file")
        exit(1)

    if instance_path != "":
        try:
            instance_program = "\n".join(open(instance_path).readlines())
        except:
            print("Could not open instance file")
            exit(1)

    split_program_rewriter = SplitProgramRewriter(encoding_program)
    solver_settings = SolverSettings(int(args.n), bool(args.debug), bool(args.constraint), split_program_rewriter.propositional_program)
    programs_handler = ProgramsHandler(split_program_rewriter.programs, instance_program)
    programs_handler.check_aspq_type()
    solver  = ASPQSolver(programs_handler, solver_settings, True, 0)
    result = solver.solve_n_levels([], "")
    if result:
        if bool(args.statistics):
            SolverStatistics().print_statistics()
        print("ASPQ SAT")
        exit(10)
    else:
        if bool(args.statistics):
            SolverStatistics().print_statistics()
        print("ASPQ UNSAT")
        exit(20)