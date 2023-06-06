import sys
import importlib

import solver

def cnf_size(cnf):
    num_clauses = len(cnf.clauses)
    terms = set()
    for clause in cnf.clauses:
        for term in clause:
            term_val = abs(int(term))
            terms.add(term_val)
    num_vars = len(terms)
    print("Clauses: {}\nVars: {}".format(
        num_clauses, num_vars))

def main():
    name = sys.argv[1]
    mpc = importlib.import_module("mpc_funcs.{}".format(name))
    s = solver.Z3Solver()
    out = s.bv('out', mpc.OUTCOME_LEN)
    cho = s.bv('chosen', mpc.CHOSEN_LEN)
    tar = s.bv('target', mpc.TARGET_LEN)
    s.add(s._eq(out, mpc.func_smt(s, cho, tar)))
    assert s.check()
    cnf_size(s.cnf())
    print("Target: {} bits".format(mpc.TARGET_LEN))
    
if __name__ == '__main__':
    main()
