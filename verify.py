import solver


def verify(mpc, C, T, correct):
    s = solver.Z3Solver()
    chosen = s.bv('chosen', mpc.CHOSEN_LEN)
    target = s.bv('target', mpc.TARGET_LEN)
    output = s.bv('output', mpc.OUTCOME_LEN)
    s.add(s._eq(chosen, s.bvconst(C, mpc.CHOSEN_LEN)))
    s.add(s._eq(target, s.bvconst(T, mpc.TARGET_LEN)))
    s.add(s._eq(mpc.func_smt(s, chosen, target), output))
    assert s.check()
    print("Verify result: {}".format(s.model('output')))
    assert s.model('output') == correct
