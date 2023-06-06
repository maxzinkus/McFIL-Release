""" mean.py
    Mean average calculation (2 inputs only), MPC functionality
"""

""" Simple test with 1 target_input (8 bits) and 1 chosen_input (8 bits) """
import math

TARGET_LEN = 8 # bit length of unknown target input
CHOSEN_LEN = TARGET_LEN # bit length of input adversary (this program) controls
OUTCOME_LEN = TARGET_LEN # bit length of the longest variable in OUTCOMES
USE_LEAKAGE = False

def func_smt(solver, chosen_input, target_input):
    """ Calculate mean between 2 numbers using bitwise operations,
        functionality inside the solver
        e.g. mean = (x + y) >> 1 # does not handle overflow
        e.g. mean = (x & y) + ((x ^ y) >> 1) # handles overflow

        note: computes the floor
    """

    # does not handle overflow
    # return solver._rshift(solver._add(chosen_input, target_input), 1)

    # handles overflow (in theory)
    cons = solver._rshift(solver._xor(chosen_input, target_input), solver.bvconst(1, CHOSEN_LEN))
    cons = solver._add(solver._and(chosen_input, target_input), cons)
    return cons

    #cons = solver.udiv(solver._add(chosen_input, target_input), solver.bvconst(2,CHOSEN_LEN))
    #x1 = solver.udiv(chosen_input, solver.bvconst(2, CHOSEN_LEN))
    #x2 = solver.udiv(target_input, solver.bvconst(2, CHOSEN_LEN))
    #cons = solver._add(x1, x2)

    #x1 = solver._rshiftbv(chosen_input, solver.bvconst(1, CHOSEN_LEN))
    #x2 = solver._rshiftbv(target_input, solver.bvconst(1, CHOSEN_LEN))
    #cons = solver._add(x1, x2)


def func(chosen_input, target_input):
    """ Calculate mean between 2 inputs, functionality outside the solver """
    #return math.floor((chosen_input + target_input) / 2)

    #x1 = int(chosen_input/2)
    #x2 = int(target_input/2)

    #x1 = chosen_input >> 1
    #x2 = target_input >> 1
    #return x1 + x2

    return (chosen_input & target_input) + ((chosen_input ^ target_input) >> 1)
