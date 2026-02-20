# Casper
Casper is a native solver based on Counter Example Abstraction Refinement (CEGAR) for 2-ASP(Q) programs (i.e., programs with at most two quantifiers), possibly with weak constraints.

In order to install and run Casper please clone this repository and then follow the instructions.

## Install
The following commands run from the root of the repository wil build and install Casper in a Python virtual environment using the venv virtual environment manager

```
python3 -m venv venv
source venv/bin/activate
pip install .
```
## Execute
usage: Casper [-h] --problem PROBLEM [--instance INSTANCE] [--debug]
              [--global-weak-lower-bound] [--no-weak] [--statistics] [--json]
              [--constraint] [-n N]

A native solver based on CEGAR for 2-ASP(Q)

options:

  -h, --help                      show this help message and exit
  
  --problem PROBLEM               path to problem file
  
  --instance INSTANCE             path to instance file
  
  --debug                         enable debug prints
  
  --global-weak-lower-bound       Apply lower bound improving for global weak
                                  constraints (default is upper bound improving)
  
  --statistics                    print solving statistics
  
  --json                          print quantified answer sets in json format - done for
                                  integration with ASPChef
  
  --constraint                    enable constraint print of models (can be used for testing) - does not apply to universal programs
  
  -n N                            number of quantified answer sets to compute (if zero enumerate) - does not apply to universal programs

By default the solver computes only one answer set and expects the instance of the problem to be inside the problem file.
However, if an instance file is specified, its content is replicated in every subprogram of the encoding

Reminders: 
-  do not break the stratified definition assumption assumed by the ASP(Q) language,
-  do not use aggregates, disjunction, conditional literals or choice rules in the second program of your encoding since they are not supported yet

All these restrictions will be removed as soon as possible.

Thank you for using Casper!
