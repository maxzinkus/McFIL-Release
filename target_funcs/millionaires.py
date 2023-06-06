""" millionaires.py
    Millionaire's problem MPC functionality
"""

TARGET_LEN = 32 # length of unknown target input
CHOSEN_LEN = TARGET_LEN # length of input adversary (this program) controls
OUTCOME_LEN = 1
USE_LEAKAGE = False
BINSEARCH = True #indicates that the optimal attack is binary search, for logging

def func_smt(solver, chosen_input, target_input):
    """ Millionaire's functionality inside the solver """
    return solver._if(solver._ugt(chosen_input, target_input), # Millionaire's
                      solver.bvconst(1,OUTCOME_LEN),
                      solver.bvconst(0,OUTCOME_LEN))

def func(chosen_input, target_input):
    """ Millionaire's functionality outside the solver """
    return chosen_input > target_input
