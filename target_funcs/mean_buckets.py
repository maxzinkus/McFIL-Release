""" mean_buckets.py
    Bucketed mean calculation (2 inputs only), MPC functionality
"""

TARGET_LEN = 32 # bit length of unknown target input
CHOSEN_LEN = TARGET_LEN # bit length of input adversary (this program) controls
OUTCOME_LEN = 6 # 2**(TARGET_LEN - OUTCOME_LEN) buckets of size 2**OUTCOME_LEN
USE_LEAKAGE = False

def func_smt(solver, chosen_input, target_input):
    """ Calculate mean between 2 numbers using bitwise operations,
        functionality inside the solver
        e.g. mean = (x + y) >> 1 # does not handle overflow
        e.g. mean = (x & y) + ((x ^ y) >> 1) # handles overflow
        note: computes the floor

        mean = mean(target_input, chosen_input)
        bucket_size = TARGET_LEN - OUTCOME_LEN (26)
        mean_bucket = mean >> bucket_size # top OUTCOME_LEN bits
        chosen_bucket = chosen_input >> bucket_size
        distance = abs(mean_bucket-chosen_bucket)
        
        Returns distance (how many buckets away was the guess from the mean)
    """
    mean_lower = solver._rshift(solver._xor(chosen_input, target_input),
                                solver.bvconst(1, CHOSEN_LEN))
    mean = solver._add(solver._and(chosen_input, target_input), mean_lower)
    mean_bucket = solver.extract(mean, TARGET_LEN-1, TARGET_LEN-OUTCOME_LEN)
    chosen_bucket = solver.extract(chosen_input, CHOSEN_LEN-1, CHOSEN_LEN-OUTCOME_LEN)
    return solver._if(solver._uge(mean_bucket, chosen_bucket),
                      mean_bucket - chosen_bucket,
                      chosen_bucket - mean_bucket)


def func(chosen_input, target_input):
    """ Calculate mean between 2 inputs, functionality outside the solver 
        Returns distance (how many buckets away was the guess from the mean)
    """
    mean = (chosen_input & target_input) + ((chosen_input ^ target_input) >> 1)
    mean_bucket = mean >> (TARGET_LEN-OUTCOME_LEN)
    chosen_bucket = chosen_input >> (CHOSEN_LEN-OUTCOME_LEN)
    return abs(mean_bucket - chosen_bucket)


