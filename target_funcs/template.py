""" template.py
    A template mpc functionality to easily create new ones
"""

TARGET_LEN =  # bit length of unknown target input
CHOSEN_LEN =  # bit length of input adversary (this program) controls
OUTCOME_LEN = # bit length of the longest variable in OUTCOMES
USE_LEAKAGE = False

def func_smt(solver, chosen_input, target_input):
    raise NotImplementedError

def func(chosen_input, target_input):
    raise NotImplementedError

