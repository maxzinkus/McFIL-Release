""" wage.py
    Wage discrimination problem, MPC functionality
"""
TARGET_LEN = 36 # length of unknown target input
CHOSEN_LEN = TARGET_LEN # length of input adversary (this program) controls
OUTCOME_LEN = 1
USE_LEAKAGE = False
BINSEARCH = True #indicates that the optimal attack is binary search, for logging

#DELTA = 0.8
NUM_EMPLOYEES = 140000 # 140,000 employees
ANNUAL_WAGES = 12000000000 # 12 billion annual wages


# Currently not calling this function
def add_addl_info(solver, target_input):
    mean = solver.bv("mean", TARGET_LEN)
    x1 = solver._add(solver.bvconst(ANNUAL_WAGES, TARGET_LEN), target_input)
    x2 = solver._add(solver.bvconst(NUM_EMPLOYEES, TARGET_LEN), solver.bvconst(1, TARGET_LEN))
    return solver._eq(solver._udiv(x1, x2), mean)

def func_smt(solver, chosen_input, target_input):
    N = solver._add(solver.bvconst(ANNUAL_WAGES, TARGET_LEN), target_input)
    D = solver.bvconst(NUM_EMPLOYEES + 1, CHOSEN_LEN)
    return solver._if(solver._uge(chosen_input,
                                  solver.bvconst(pow(2,TARGET_LEN)//(NUM_EMPLOYEES+1),
                                                 CHOSEN_LEN)),
                      solver.bvconst(0, OUTCOME_LEN),
                      solver._if(solver._ult(solver._mult(chosen_input, D), N),
                        solver.bvconst(1,OUTCOME_LEN),
                        solver.bvconst(0,OUTCOME_LEN)))

def func(chosen_input, target_input):
    # x1 = ANNUAL_WAGES + target_input
    # x2 = NUM_EMPLOYEES + 1
    # mean = int(x1 / x2)
    # return chosen_input < mean

    N = ANNUAL_WAGES + target_input
    D = NUM_EMPLOYEES + 1

    if chosen_input >= pow(2, TARGET_LEN) // D:
        return 0
    return int((chosen_input*D) < N)


