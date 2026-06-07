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
import sys
import signal
import argparse
from clingo.ast import parse_string
from casper.utils import SolverStatistics
from casper.utils import SolverSettings
from casper.rewriters import SplitProgramRewriter
from casper.rewriters import WeakRewriter
from casper.solver import ProgramsHandler
from casper.solver import ASPQSolver
from casper.rewriters.disjunction import DisjunctionRewriter


def _handle_signal(signum, frame):
    SolverStatistics().print_statistics()
    print("Sig term")
    sys.stdout.flush()
    sys.exit(124)

def entrypoint():
    signal.signal(signal.SIGTERM, _handle_signal)
    signal.signal(signal.SIGINT, _handle_signal)
    parser = argparse.ArgumentParser(prog = "Casper", description = "A native solver based on CEGAR for 2-ASP(Q)\n")

    parser.add_argument('--problem', help="path to problem file\n", required=True)
    parser.add_argument('--instance', help="path to instance file\n", required=False, default="")
    parser.add_argument('--debug', help="enable debug\n", required=False, action="store_true")
    parser.add_argument('--global-weak-lower-bound', help="Apply lower bound improving for global weak constraints (default is upper bound improving)\n", required=False, action="store_true")
    parser.add_argument('--no-weak', help="completely remove weak constraints before solve optimization ASP(Q) programs\n", required=False, action="store_true")
    parser.add_argument('--statistics', help="print solving statistics\n", required=False, action="store_true")
    parser.add_argument('--json', help="print quantified answer sets in json format - done for integration with ASPChef\n", required=False, action="store_true")
    parser.add_argument('--constraint', help="enable constraint print of models\n", required=False, action="store_true")
    parser.add_argument('--disjunction', help="enable disjunction in the solver\n", required=False, action="store_true")
    parser.add_argument('-n', help="number of q-answer sets to compute (if zero enumerate)\n", default=1)
    parser.add_argument('--blocking-ref', help="Applies a weaker refinement transformation based on blocking clauses only\n", required=False, action="store_true")
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


    collapse_global_weak_in_p1 = bool(args.global_weak_lower_bound)
    split_program_rewriter = SplitProgramRewriter(encoding_program, bool(args.disjunction))
    solver_settings = SolverSettings(int(args.n), bool(args.debug), bool(args.constraint), split_program_rewriter.pure_choice, bool(args.no_weak), collapse_global_weak_in_p1, bool(args.json), bool(args.blocking_ref))
    
    # for program in split_program_rewriter.programs:
    #     if program.contains_choice:
    #         print("Cannot handle programs with choice rules")
    #         exit(1)

    programs = split_program_rewriter.programs
    global_weak = split_program_rewriter.global_weak

    if split_program_rewriter.program_contains_disjunction():
        if split_program_rewriter.program_contains_weak():
            print("Cannot handle weak costraints for disjunctive programs")
            exit(1)
        else:
            disjunction_rewriter = DisjunctionRewriter(programs)
            programs = disjunction_rewriter.rewrite()
            for program in programs:
                print(program)
                print(program.head_predicates)
            
    problem_has_global_weak = False

    if not global_weak is None and collapse_global_weak_in_p1:
        problem_has_global_weak = True

    weak_rewriter = WeakRewriter(programs, global_weak, solver_settings.no_weak, collapse_global_weak_in_p1)
    #check if rewritten program contains weak (for example, in \exists_weak \exist programs weak are never rewritten) 
    solver_settings.no_weak = solver_settings.no_weak or weak_rewriter.rewritten_program_contains_weak
    
    programs_handler = ProgramsHandler(weak_rewriter.rewritten_program(), instance_program, weak_rewriter.global_weak)
    programs_handler.check_aspq_type()
    if programs_handler.program_contains_weak():
        solver_settings.n_models = 1
    solver  = ASPQSolver(programs_handler, solver_settings, True, 0)
    result = solver.solve_n_levels([], "")
    if result:
        if bool(args.statistics):
            SolverStatistics().print_statistics()
        if not solver_settings.json_format:
            print("ASPQ SAT")
        if problem_has_global_weak:
            exit(30)
        exit(10 if not solver.optimum_found else 30)
    else:
        if bool(args.statistics):
            SolverStatistics().print_statistics()
        if not solver_settings.json_format:
            print("ASPQ UNSAT")
        exit(20)