""" dualexecution_affine.py
"""
from functools import reduce

TARGET_LEN = 12 # bit length of unknown target input
CHOSEN_LEN = TARGET_LEN+pow(TARGET_LEN, 2) # bit length of input adversary (this program) controls
OUTCOME_LEN = 1 # bit length of the longest variable in OUTCOMES
USE_LEAKAGE = False

def func_smt(solver, chosen_input, target_input):
    matrix_bits = solver.extract(chosen_input, CHOSEN_LEN-1, TARGET_LEN)
    chosen_input = solver.extract(chosen_input, TARGET_LEN-1, 0)
    matrix = [[solver.extract(matrix_bits, j*TARGET_LEN+i, j*TARGET_LEN+i)
               for i in range(TARGET_LEN)] for j in range(TARGET_LEN)]
    chosen_bits = [solver.extract(chosen_input, i, i) for i in range(TARGET_LEN)]
    target_bits = [solver.extract(target_input, i, i) for i in range(TARGET_LEN)]
    chosen_matrix = [reduce(lambda x, y: solver._add(x, y),
                            [solver._mult(matrix[j][i], chosen_bits[i])
                             for i in range(TARGET_LEN)])
                     for j in range(TARGET_LEN)]
    target_matrix = [reduce(lambda x, y: solver._add(x, y),
                            [solver._mult(matrix[j][i], target_bits[i])
                             for i in range(TARGET_LEN)])
                     for j in range(TARGET_LEN)]
    chosen_out = solver.concat(*reversed(chosen_matrix))
    target_out = solver.concat(*reversed(target_matrix))
    return solver._if(solver._eq(chosen_out, target_out),
                      solver.bvconst(1,1),
                      solver.bvconst(0,1))

def func(chosen_input, target_input):
    matrix_bits = chosen_input >> TARGET_LEN
    chosen_input = chosen_input & ((1 << TARGET_LEN)-1)
    matrix = [[(matrix_bits >> (i+TARGET_LEN*j)) & 1 for i in range(TARGET_LEN)]
              for j in range(TARGET_LEN)]
    chosen_bits = [(chosen_input >> i) & 1 for i in range(TARGET_LEN)]
    target_bits = [(target_input >> i) & 1 for i in range(TARGET_LEN)]
    chosen_matrix = [sum([(matrix[j][i]*chosen_bits[i])%2 for i in range(TARGET_LEN)])
                        % 2
                     for j in range(TARGET_LEN)]
    target_matrix = [sum([(matrix[j][i]*target_bits[i])%2 for i in range(TARGET_LEN)])
                        % 2
                     for j in range(TARGET_LEN)]
    chosen_out = 0
    for i, bit in enumerate(chosen_matrix):
        chosen_out |= bit << i
    target_out = 0
    for i, bit in enumerate(target_matrix):
        target_out |= bit << i
    return 1 if chosen_out == target_out else 0
