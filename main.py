""" main.py
    Given a description of an functionality in the form of:
    * func_smt (function)
        arguments:
            - solver instance
            - solver variable representing adversary (this program) input
            - solver variable representing honest party input to be discovered
        return value (integer):
            - solver expression representing the functionality as a constraint
            - use 0/1 for False/True
    * func (function)
        arguments:
            - input a
            - input b
        return value:
            - computed result of the functionality
    * leak (function) [optional]
        (not implemented)
    * TARGET_LEN (integer)
        bit length of the secret input (may be overridden with --target-length)
    * CHOSEN_LEN (integer)
        bit length of the chosen input (may be overridden with --chosen-length)
    * OUTCOMES (list)
        list of booleans or bitvectors (represented as integers) representing
        the possible outputs of the functionality
        (special case: empty list sets OUTCOMES to all bitstrings of length
            OUTCOME_LEN)
    * OUTCOME_LEN (integer)
        an integer representing the maximum bit length of an outcome in
            OUTCOMES
        (special case:  OUTCOME_LEN=1 sets OUTCOMES to [True, False])
    * SECRET (integer) [OPTIONAL]
        concrete value (as an integer) of the target input
        if unset, a random value will be generated

    this program will attempt to iteratively derive and add constraints to
    compute solution(s) for the honest party's input to the functionality.
"""
import os
import time
import random
import argparse
import binascii
import importlib
from math import log2
import multiprocessing as mp
import matplotlib.pyplot as plt

import solver as libsolver

CONTINUE = None
SMT2_DIR = "benchmarks"


def configure_outcomes(solver, f_smt, target_len, outcomes, outcome_len,
                       chosen_len, num_trials):
    for outcome in outcomes:
        outcome_bv = solver.bvconst(outcome, outcome_len)
        oc_chosen = solver.bv("chosen_outcome{}".format(outcome), chosen_len)
        for trial in range(num_trials):
            oc_target = solver.bv(
                "target_outcome{}_t{}".format(outcome, trial), target_len)
            solver.add(solver._eq(f_smt(solver, oc_chosen, oc_target),
                                  outcome_bv))


def mp_approxmc(outcome, cnf, indep):
    s = libsolver.Z3Solver()
    count, duration = s.approxmc(cnf=cnf, indep=indep)
    return (outcome, count, duration)


def select_outcomes(solver, f_smt, chosen_input, outcomes, outcome_len,
                    target, target_len, num_trials, knownbits, skip):
    """ Pre-query solver setup to create requisite variables & constraints """
    if not skip:
        print("Determining outcome profitability...")
    real_appmc_time = time.time()
    total_appmc_time = 0
    outcomes_results = {}
    promises = []
    global POOL
    progress = 0
    for i, outcome in enumerate(outcomes):
        solver.push()
        outcome_bv = solver.bvconst(outcome, outcome_len)
        solver.add(solver._eq(f_smt(solver, chosen_input, target),
                              outcome_bv))
        cnf = solver.cnf()
        solver.pop()
        indep = [cnf.variables["target_{}".format(var)] for var in filter(
                    lambda i: knownbits[i] == '?',
                    range(target_len))]
        try:
            if not skip:
                promise = POOL.apply_async(mp_approxmc, (outcome, cnf, indep))
        except Exception as e:
            POOL.terminate()
            raise e
        if not skip:
            if int((i/len(outcomes))*100) > progress:
                print("-", end="", flush=True)
                progress = int((i/len(outcomes))*100)
            promises.append(promise)
    progress = 0
    if not skip:
        print(" generated")
        for i, promise in enumerate(promises):
            outcome, count, duration = promise.get()
            if int((i/len(promises))*100) > progress:
                print("-", end="", flush=True)
                progress = int((i/len(promises))*100)
            outcomes_results[outcome] = count
            total_appmc_time += duration
        print(" solved")
    else:
        outcomes_results[outcome] = 1
    outcomes_counts = []
    for outcome, count in outcomes_results.items():
        if count > 0:
            oc_chosen = solver.bv("chosen_outcome{}".format(outcome))
            outcomes_counts.append((outcome, oc_chosen, count))
    if not skip:
        print("Parallel ApproxMC took {}s ({}s cpu, avg {}s/oc, {} ocs)".format(
            round(time.time() - real_appmc_time, 3),
            round(total_appmc_time, 3),
            round(total_appmc_time/float(len(outcomes)), 3),
            len(outcomes)))
    """
    print("Outcomes: {}".format(
        ", ".join(["{} ({})".format(o, c) for (o,_,c) in outcomes_counts])))
    """
    if not skip:
        print("Computing maximal outcome set...")
    # sort by approxmc count
    outcomes_counts.sort(key=lambda oc: oc[2])
    found_outcome_set = skip # if skip is true, we're done, so set found = true
    while not found_outcome_set:
        solver.push()
        for (_, oc_chosen, _) in outcomes_counts:
            solver.add(solver._eq(chosen_input, oc_chosen))
        found_outcome_set = solver.check()
        solver.pop()
        if not found_outcome_set:
            if outcomes_counts:
                outcomes_counts.pop(0)  # remove the smallest class
            if len(outcomes_counts) < 2:
                print("Warning: unable to constrain.")
                global CONTINUE
                if CONTINUE is None:
                    CONTINUE = input("Continue? [Y/n] ").lower() != 'n'
                if not CONTINUE:
                    raise KeyboardInterrupt
                return {}
    if skip:
        print("Skipped SelectOutcomes (by user configuration)")
    print("# Outcomes: {}".format(len(outcomes_counts)))
    target_vars = {}
    for (outcome, oc_chosen, _) in outcomes_counts:
        solver.add(solver._eq(chosen_input, oc_chosen))
        for trial in range(num_trials):
            oc_target = solver.bv(
                "target_outcome{}_t{}".format(outcome, trial))
            target_vars[oc_target] = outcome
    return target_vars


def mp_modelcount(cms_args):
    cnf, size, target_vars_bits_names, k_xor_size, indices = cms_args
    for target_bits_names in target_vars_bits_names:
        for _ in range(size):
            # choose a random xor
            random.shuffle(indices)
            xor = []
            for i in indices[:k_xor_size]:
                bit = target_bits_names[i]
                cnf_bit = cnf.variables[bit]
                xor.append(cnf_bit)
            prefix = "" if random.randint(0, 1) > 0 else "-"
            xor += [prefix+cnf.variables["_true"]]
            cnf.xors.append(xor)
    result, model, duration = cnf.check_cms(xor_size=k_xor_size,
                                            filename="size:{}_".format(size))
    if result:
        reverse_map = {v: k for k, v in cnf.variables.items()}
        model = {reverse_map[name]: val for name, val in model.items()}
    return (size, result, model, duration)


def compute_next_query(solver, chosen_input, chosen_len, target_vars,
                       indep_vars, k_xor_size, args):
    """ Use simultaneous maximization of outcome classes to generate a greedy
        attack via chosen input queries
    """
    # Set up target variables for xor application
    solver.push()
    target_vars_bits = []
    target_vars_bits_map = {}
    for target, outcome in target_vars.items():
        target_bits = []
        target_bools = []
        for i in indep_vars:
            target_bits.append(solver.extract(target, i, i))
            # BEGIN z3-specific mapping
            name = "target_bit_{}_{}_bool".format(outcome, i)
            _bool = solver.bool(name)
            target_bools.append((name, _bool))
            target_vars_bits_map[name] = _bool
        for bit, (_, _bool) in zip(target_bits, target_bools):
            solver.add(solver._iff(solver._eq(bit, solver.bvconst(1, 1)),
                                   solver._iff(_bool, solver.true())))
        target_bits = target_bools
        # END z3-specific mapping
        target_vars_bits.append(target_bits)
    # Apply maximization constraints to get optimal (greedy) query
    query = None
    indices = list(range(len(indep_vars)))
    global POOL
    cnf = solver.cnf(add_true=True)
    if not args.no_bench:
        smt2_file = os.path.join(SMT2_DIR, args.mpc_func_file)
        if not os.path.isdir(smt2_file):
            os.mkdir(smt2_file)
        smt2_filename = '.'.join(
            (args.mpc_func_file,
             "t"+str(args.num_trials), "i"+str(len(indep_vars)),
             binascii.hexlify(os.urandom(4)).decode('ascii'), "smt2"))
        smt2_filename = os.path.join(smt2_file, smt2_filename)
        with open(smt2_filename, 'w') as f:
            f.write(solver.smt2())
            print(f"Saved smt2 to {smt2_filename}")
        cnf_filename = smt2_filename.replace(".smt2", ".cnf")
        with open(cnf_filename, 'w') as f:
            f.write(str(cnf))
            print(f"Saved cnf to {cnf_filename}")
    solver.pop()
    target_vars_bits_names = [[name for name, _ in target_var_bits]
                              for target_var_bits in target_vars_bits]
    sizes = list(range(len(indep_vars)))
    cms_results = {}
    cms_args = [(cnf, size, target_vars_bits_names, k_xor_size, indices)
                for size in sizes]
    print("Computing next query...")
    real_cms = time.time()
    try:
        for size, sat, model, duration in POOL.imap_unordered(mp_modelcount,
                                                              cms_args):
            cms_results[size] = (sat, model, duration)
    except Exception as e:
        POOL.terminate()
        raise e
    # for largest size, convert model to z3
    total_cms = 0
    final_model = None
    print("Collecting CMS result")
    for size in reversed(sizes):
        sat, model, duration = cms_results[size]
        total_cms += duration
        if sat:
            print("Success at size 2**{}".format(size))
            final_model = model
            break
    print("Parallel CMS took {}s ({}s cpu)".format(
        round(time.time()-real_cms, 3),
        round(total_cms, 3)))
    query = 0
    for i in range(chosen_len):
        if final_model["chosen_{}".format(i)]:
            query |= (1 << i)
    return query


def add_iterative_constraints(solver, f_smt, target_input, target_vars,
                              query, result, outcome_len):
    """ Update the solver with what we learned this round """
    result_bv = solver.bvconst(result, outcome_len)
    solver.add(solver._eq(f_smt(solver, query, target_input),
                          result_bv))
    # query was not None, so the solver must have been satisfiable
    knownbits = solver.knownbits("target")
    # but adding the query result might make the solver unsat for some outcomes
    if '?' in knownbits:
        for oc_target, outcome in target_vars.items():
            if result != outcome:
                solver.push()
                solver.add(solver._eq(f_smt(solver, query, oc_target),
                                      result_bv))
                valid_outcome = solver.check()
                solver.pop()
                if valid_outcome:
                    solver.add(solver._eq(f_smt(solver, query, oc_target),
                                          result_bv))
                else:
                    solver.add(solver._not(solver._eq(
                        target_input, oc_target)))
    return knownbits


def main(args):
    """ Run the attack (for docs see top of file) """
    # Import target functionality and set up global variables
    global mpc
    mpc = importlib.import_module("target_funcs.{}".format(args.mpc_func_file))
    chosen_len = mpc.CHOSEN_LEN
    target_len = mpc.TARGET_LEN
    outcome_len = mpc.OUTCOME_LEN
    if outcome_len <= 0:
        raise ValueError("OUTCOME_LEN must be >= 1")

    # Unpack arguments
    num_trials = args.num_trials
    if num_trials < 1:
        raise ValueError("num_trials must be >= 1")
    if args.xor_size == "log2":
        def xor_size(indep_vars):
            return int(round(log2(len(indep_vars))))
    elif args.xor_size == "frac":
        def xor_size(indep_vars):
            return int(round(len(indep_vars)/2))
    else:
        raise ValueError("Invalid option: -k/--xor-size {}".format(xor_size))
    # Optionally override configurations
    if args.chosen_len is not None:
        chosen_len = args.chosen_len
    if args.target_len is not None:
        target_len = args.target_len
    if args.no_guess:
        global CONTINUE
        CONTINUE = False

    # Initialize the solver and the "oracle"
    solver = libsolver.Z3Solver()
    try:
        oracle = Oracle(mpc.SECRET, mpc.func)
    except AttributeError:
        oracle = Oracle(random.randrange(0, pow(2, target_len)), mpc.func)
    print("Secret: {}".format(oracle.secret))
    chosen_input = solver.bv("chosen", chosen_len)
    chosen_bits = [
        solver.extract(chosen_input, i, i) for i in range(chosen_len)]
    chosen_bools = [
        solver.bool("chosen_{}".format(i)) for i in range(chosen_len)]
    for bit, _bool in zip(chosen_bits, chosen_bools):
        solver.add(solver._iff(solver._eq(bit, solver.bvconst(1, 1)),
                               solver._iff(_bool, solver.true())))
    target_input = solver.bv("target", target_len)
    # z3-specific: booleans for CNF mapping
    for i in range(target_len):
        bit = solver.extract(target_input, i, i)
        _bool = solver.bool('target_{}'.format(i))
        solver.add(solver._iff(solver._eq(bit, solver.bvconst(1, 1)),
                               solver._iff(_bool, solver.true())))
    # end z3-specific
    """
    try:
        solver.add(mpc.add_addl_info(solver, target_input))
    except AttributeError:
       pass
    """

    # Initialize constraints and solver variables for functionality (f_smt)
    # Define via func_smt, and reverse-enumerate outcomes
    solver.push()
    outcomes = set()
    outcome_derivation = solver.bv("outcome_deriv", outcome_len)
    solver.add(solver._eq(mpc.func_smt(solver, chosen_input, target_input),
                          outcome_derivation))
    while solver.check():
        new_outcome = solver.model("outcome_deriv")
        outcomes.add(new_outcome)
        new_outcome_bv = solver.bvconst(new_outcome, outcome_len)
        solver.add(solver._not(solver._eq(outcome_derivation, new_outcome_bv)))
    solver.pop()
    if not outcomes:
        raise ValueError("func_smt must be satisfiable")
    if len(outcomes) == 1:
        raise ValueError("func_smt must have multiple possible outputs")

    # Initial solver setup (chosen for each outcome, targets for each trial and
    # outcome)
    configure_outcomes(solver, mpc.func_smt, target_len, outcomes, outcome_len,
                       chosen_len, num_trials)

    # Main loop: iteratively derive queries, query the oracle, and constrain,
    # checking progress using knownbits
    knownbits = solver.knownbits("target")
    query = not None
    queries = []
    counts = []
    start_loop = time.time()
    global POOL
    # POOL = mp.Pool(max(len(os.sched_getaffinity(0))-8, 8)) # linux only
    POOL = mp.Pool(os.cpu_count())
    while '?' in knownbits and query is not None:
        print("Starting iteration {}".format(len(queries)))
        try:
            indep_vars = []
            for i, bit in enumerate(knownbits):
                if bit == '?':
                    indep_vars.append(i)

            solver.push()
            # target_vars contains a dictionary of variables to maximize over
            # and the outcome each variable maps to
            if CONTINUE:
                target_vars = {}
            else:
                target_vars = select_outcomes(
                    solver, mpc.func_smt, chosen_input, outcomes, outcome_len,
                    target_input, target_len, num_trials, knownbits, args.skip_select)

            # Derive a new query
            query = compute_next_query(
                solver, chosen_input, chosen_len, target_vars, indep_vars,
                xor_size(indep_vars), args)
            solver.pop()
            # Query the oracle and update constraints
            if query is not None:
                if query in queries:
                    raise ValueError("Duplicate query: {}".format(query))
                print("Query: {}".format(query))
                count = None
                if args.approxmc or args.graph_count:
                    cnf = solver.cnf()
                    indep = [cnf.variables["target_{}".format(i)]
                             for i in filter(
                                 lambda i: knownbits[i] == '?',
                                 range(target_len))]
                    count, duration = solver.approxmc(indep=indep)
                    if args.approxmc:
                        print("ApproxMC remaining solutions: {}".format(count))
                        print("ApproxMC finished in {}s".format(duration))
                queries.append(query)
                counts.append(count)
                result = oracle.compute(query)
                print("Result: {}".format(result))
                """
                import verify
                verify.verify(mpc, query, oracle.secret, result)
                """
                query_var = solver.bvconst(query, chosen_len)
                knownbits = add_iterative_constraints(
                    solver, mpc.func_smt, target_input, target_vars,
                    query_var, result, outcome_len)
                solver.add(solver._not(solver._eq(chosen_input, query_var)))
                if not solver.check():
                    print("No remaining queries to try.")
                    query = None
                    break
            print("Secret: " + ''.join(knownbits) + "\n")
        except KeyboardInterrupt:
            POOL.terminate()
            knownbits = solver.knownbits("target")
            break
        except Exception as e:
            POOL.terminate()
            raise e
    # End of main loop
    POOL.close()

    # Print results
    iterations = len(queries)
    print("Completed after {} iterations ({}s)".format(
        iterations, time.time()-start_loop))
    print("Final result: {}".format(''.join(knownbits)))
    if '?' not in knownbits:
        print("As int: {}".format(int(''.join(reversed(knownbits)), 2)))
    try:
        print("Secret: {}".format(oracle.secret))
        match = False
        for i, bit in enumerate(knownbits):
            if bit == '?':
                continue
            bit = int(bit)
            if (oracle.secret >> i) & 1 != bit:
                print("Mismatch at index {}".format(i))
                match = False
            else:
                match = True
        if match:
            result = "Success"
            if '?' in knownbits:
                result += " (partial: {} of {} bits)".format(
                        target_len-knownbits.count('?'), target_len)
            if iterations > 0:
                print("Learned {} bits/query".format(
                        round((target_len-knownbits.count('?'))/iterations, 5)))
        else:
            result = "Failure"
        print(result)
    except AttributeError:
        pass

    # Generate log and graph(s)
    if args.log:
        for query, count in zip(queries, counts):
            args.log.write("Q:{}\nC:{}\n".format(query, count))
    if args.graph_queries:
        filename = args.graph_queries
        if filename == "auto":
            filename = '.'.join((args.mpc_func_file, "queries",
                                 "t"+str(args.num_trials),
                                 str(int(round(time.time()))), "png"))
        try:
            if mpc.BINSEARCH:
                correct = list(map(log2, oracle.binsearch(0,
                                                          pow(2, chosen_len))))
                print("True Binary Search")
                print(",".join(oracle.binsearch(0, pow(2, chosen_len))))
                plt.plot(list(range(len(correct))), correct, c='red')
        except AttributeError:
            pass
        print("Queries")
        print(",".join(queries))
        plt.title("Log query value over queries")
        # tight range to better display values
        plt.ylim([min(list(map(log2, queries)))-1, chosen_len+1])
        plt.scatter(list(range(iterations)), list(map(log2, queries)))
        plt.savefig(filename)
        plt.clf()
    if args.graph_count:
        filename = args.graph_count
        if filename == "auto":
            filename = '.'.join((args.mpc_func_file, "counts",
                                 "t"+str(args.num_trials),
                                 str(int(round(time.time()))), "png"))
        plt.title("Log remaining solutions over queries")
        plt.ylim([0, target_len+1])
        plt.scatter(list(range(iterations)), list(map(log2, counts)))
        plt.savefig(filename)
        plt.clf()

    # Final cleanup
    POOL.join()


class Oracle:
    """ Simple oracle class for protocol analysis
        only required method is compute, which may be implemented via true MPC
        protocol execution
    """
    def __init__(self, secret, func):
        self.secret = secret
        self.func = func

    def compute(self, query):
        """ Represents executing the MPC """
        return self.func(query, self.secret)

    def binsearch(self, _min, _max):
        """ generate true binary search as point of comparison """
        searches = []
        while _min not in (_max-1, _max):
            search = (_min//2) + (_max//2)
            searches.append(search)
            if search <= self.secret:
                _min = search
            else:
                _max = search
        assert _min == self.secret
        return searches


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description="Test attack algorithm against provided functionality")
    parser.add_argument("-s", "--skip", dest="skip_select", action='store_true',
                        default=False,
                        help="skip SelectOutcomes; use only if functionality is known complete")
    parser.add_argument("-t", "--trials", dest="num_trials", type=int,
                        default=1,
                        help="controls model count accuracy (>= 1)")
    parser.add_argument("-k", "--xor-size", dest="xor_size", type=str,
                        choices=("log2", "frac"),
                        default="log2",
                        help="controls model count accuracy\n\
                                log2: faster, decreased formal guarantees\n\
                                frac: slower, increased formal guarantees")
    parser.add_argument("-l", "--use-leakage", action='store_true',
                        default=False, dest='use_leakage',
                        help="enables modeling of additional (external) \
                        leakage [not yet implemented]")
    parser.add_argument("-g", "--no-guess", action='store_true',
                        default=False, dest='no_guess',
                        help="don't attempt brute-force search if \
                        constraining fails")
    parser.add_argument("-b", "--no-bench", action='store_true',
                        default=False, dest='no_bench',
                        help="don't write out smt2 and cnf for benchmarks dataset")
    parser.add_argument("--log", type=argparse.FileType('w'), default=None,
                        metavar="LOGFILE",
                        help="file to log queries as ints, one per line ('-' \
                        for stdout)")
    parser.add_argument("--graph-queries", dest="graph_queries", type=str,
                        default="", metavar="FILENAME|auto",
                        help="file to store graph of query integers \
                        over query number ('auto' to auto-name based on \
                        parameters)")
    parser.add_argument("--graph-count", dest="graph_count", type=str,
                        default="", metavar="FILENAME|auto",
                        help="file to store graph of ApproxMC remaining model \
                        count over query number (supports 'auto')")
    parser.add_argument("--approxmc", action='store_true',
                        help="print ApproxMC count at each iteration")
    parser.add_argument("--target-length", dest="target_len", type=int,
                        help="override TARGET_LEN for testing")
    parser.add_argument("--chosen-length", dest="chosen_len", type=int,
                        help="override CHOSEN_LEN for testing")
    parser.add_argument("mpc_func_file", type=str,
                        help="file in target_funcs/ containing target \
                        functionality")
    main(parser.parse_args())
