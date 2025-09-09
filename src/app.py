from .SolverSettings import SolverSettings
from .ASPQSolver import ASPQSolver
import argparse
import os

def entrypoint():
    parser = argparse.ArgumentParser(prog = "Casper", description = "A native solver based on CEGAR for 2-ASP(Q)\n")

    parser.add_argument('--problem', help="path to problem file\n", required=True)
    parser.add_argument('--instance', help="path to instance file\n", required=False, default="")
    parser.add_argument('--debug', help="enable debug\n", required=False, action="store_true")
    parser.add_argument('--constraint', help="enable constraint print of models\n", required=False, action="store_true")
    parser.add_argument('--relaxed', help="pick first model as a model of the union of relaxed programs\n", required=False, action="store_true")
    parser.add_argument('-n', help="number of q-answer sets to compute (if zero enumerate)\n", default=1)
    args = parser.parse_args()
    solver_settings = SolverSettings(int(args.n), bool(args.debug), bool(args.constraint), bool(args.relaxed))
    solver  = ASPQSolver(args.problem, args.instance, solver_settings)
    solver.ground()
    solver.solve()