# Casper
Casper is a solver based on Counterexample-Guided Abstraction Refinement (CEGAR) for ASP(Q).

In order to install and run Casper please clone this repository and then follow the instructions.

## Install
The following commands run from the root of the repository wil build and install Casper in a Python virtual environment using the venv virtual environment manager

```
python3 -m venv venv
source venv/bin/activate
pip install .
```
## Execute
usage: casper [-h] --problem PROBLEM [--instance INSTANCE] [--debug] [--global-weak-lower-bound] [--no-weak] [--statistics] [--json] [--constraint] [--disjunction] [-n N] [--blocking-ref] [--solve-limit SOLVE_LIMIT]

A CEGAR-based solver for ASP(Q)

options:
  -h, --help                    show this help message and exit
  --problem PROBLEM             path to problem file
  --instance INSTANCE           path to instance file
  --debug                       enable debug
  --global-weak-lower-bound     Apply lower bound improving for global weak constraints (default is upper bound improving)
  --no-weak                     completely remove weak constraints before solve optimization ASP(Q) programs
  --statistics                  print solving statistics
  --json                        print quantified answer sets in json format
  --constraint                  enable constraint print of models
  --disjunction                 enable disjunction in the solver
  -n N                          number of q-answer sets to compute (if zero enumerate) does not apply to universal programs as well as to programs with weak constraints
  --blocking-ref                Applies a weaker refinement transformation based on blocking clauses only
  --solve-limit SOLVE_LIMIT     maximum number of countermoves that the solver explores before terminating - by default no bound is set

By default the solver computes only one quantified answer set for existential programs (resp. decides the coherence of universal one) and expects the instance of the problem to be inside the problem file.
However, if an instance file is specified, its content is replicated in every subprogram of the encoding.

Reminders: 
-  do not break the stratified definition assumption assumed by the ASP(Q) language
-  do not use disjunction or conditional literals since they are not supported yet

All these restrictions will be removed as soon as possible.

Thank you for using Casper!
