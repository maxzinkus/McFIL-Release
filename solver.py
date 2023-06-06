""" solver.py: interface to z3
    Supports CNF(XOR) constraint generation, CNF(XOR) generation, and
        model counting
"""
import os
import time
import copy
import subprocess
from tempfile import NamedTemporaryFile, gettempdir

import z3

LOUVAIN_LIBS="~/louvain-community/build/lib"

# CryptoMinisat returns these exit codes for SAT and UNSAT
# for some unholy reason
CMS_SAT = 10
CMS_UNSAT = 20

class CNF:
    """ Represent CNF formulae """
    def __init__(self):
        self.clauses = []
        self.xors = [] # list of lists of variables to be xor'd together (CMS)
        self.variables = {}
        self.var = 1 # variable names start at 1

    def newvar(self):
        """ Add a new variable to the formula """
        var_name = str(self.var)
        self.var += 1
        return var_name

    def __str__(self):
        header = "p cnf {} {}\n".format(len(self.variables),
                                        len(self.clauses)+len(self.xors))
        body = ""
        for clause in self.clauses:
            c_str = " ".join(clause) + " 0\n"
            body += c_str
        for xor in self.xors:
            x_str = "x" + " ".join(xor) + " 0\n"
            body += x_str
        return header+body

    def write(self, filename=None, tmpdir=gettempdir(), mis=False):
        """ write cnf out to a temporary file
            unused because we usually do str(solver.cnf())
        """
        ext = ".cnf"
        if filename is None:
            fopen = NamedTemporaryFile
            fargs = {'mode': 'w+', 'dir': tmpdir, 'suffix': ext, delete: False}
        else:
            fopen = open
            fargs = {'filename': filename+ext, 'mode': 'w+'}
        with fopen(**fargs) as f:
            filename = f.name
            str_repr = str(self)
            f.write(str_repr)
            if mis:
                if self.xors:
                    raise ValueError("Cannot compute mis over .cnfxor")
                f.seek(0)
                indvars = mis(filename)
                f.write("c ind {}\n".format(indvars))
                f.write(str_repr)
        return filename

    def check_cms(self, xor_size=0, filename=None, verbose=False, silent=True, arjun=False):
        with NamedTemporaryFile(mode='w+', dir=gettempdir(), prefix=filename, suffix=".cnf") as f:
            write_stream = str(self)
            cnf_duration = 0
            f.write(write_stream)
            f.seek(0)
            if arjun:
                if verbose:
                    print("Running Arjun...")
                try:
                    output = subprocess.check_output(
                            ['arjun', '--recomp', '1', f.name]).split(b"\n")
                    f.seek(0)
                except subprocess.CalledProcessError as e:
                    print("Arjun error")
                    f.seek(0)
                    os.system("cp {} {}".format(f.name, "{}.arjunerror".format(f.name)))
                    raise e
                results = []
                appending = False
                for line in output:
                    if line.startswith(b"c ind"):
                        appending = True
                    if appending:
                        results.append(line)
                    else:
                        continue
                    if line.endswith(b" 0"):
                        break
                results = b" ".join(results)
                try:
                    indep = [int(x) for x in results.split(b" ")[2:-1]]
                except (IndexError, ValueError) as e:
                    print("Error parsing Arjun output")
                    raise e
                f.write("c ind {} 0\n".format(" ".join([str(x) for x in indep])))
                f.write(write_stream)
                f.seek(0)
            if verbose:
                print("Running CryptoMinisat...")
            cms_start = time.time()
            if xor_size > 0:
                popen_args = ['cryptominisat5', '--maxxorsize', str(min(xor_size, 8)), f.name]
            else:
                popen_args = ['cryptominisat5', f.name]
            try:
                subprocess.check_output(popen_args, encoding="ascii")
                raise ValueError("CryptoMinisat return code: 0 (abnormal)")
            except subprocess.CalledProcessError as ret:
                cms_duration = time.time() - cms_start
                model = {}
                if ret.returncode == CMS_SAT:
                    result = True
                    for line in filter(lambda l: l.startswith("v"), ret.output.split("\n")):
                        for token in line.split(" "):
                            if token in ("v", "", "0"):
                                continue
                            if token.startswith("-"):
                                model_bit = False
                                token = token[1:]
                            else:
                                model_bit = True
                            model[token] = model_bit
                elif ret.returncode == CMS_UNSAT:
                    result = False
                else:
                    from binascii import hexlify
                    err_file = "err{}.{}.cnf".format(ret.returncode, hexlify(os.urandom(10)).decode('ascii'))
                    if os.path.exists("./errors") and not os.path.isdir("./errors"):
                        os.remove("./errors")
                    if not os.path.exists("./errors"):
                        os.mkdir("./errors")
                    with open("./errors/"+err_file, 'w') as err:
                        f.seek(0)
                        err.write(f.read())
                    raise ValueError("CryptoMinisat return code: {}, saved output: {}".format(ret.returncode, "errors/"+err_file))
                if verbose:
                    print("CryptoMinisat finished in {}s".format(cms_duration))
            return result, model, cnf_duration+cms_duration

class SolverInterface:
    """
        check() -> bool
        add([constraints]) -> None
        bv(name, length) -> bitvector
        _bool(bool) -> boolean value
        true() -> boolean value
        false() -> boolean value
        bvconst(value, length) -> bitvector value
        _not(expr) -> expr
        _SHIFT(bv, i) -> bv
            SHIFT = {lshift, rshift}
        _BINOP(expr, expr) -> expr
            BINOP = {and, or, xor, eq, mult, ule, uge, ult, ugt}
        _if(expr, expr, expr) -> expr
        _mod(expr, i) -> expr
        push() -> None
        pop() -> None
        model([names]) -> {(name: value) for name in names}
        assertions() -> [constraints]
        bvlen(name) -> size
        extract(bv, high, low) -> bv
        knownbits(name) -> [{'0', '1', '?'}, ...]
        mbound(size, t, delta, k, bvs, subset) -> expr
        exact(name) -> count
        atleastx(name, x) -> bool
        approxmc() -> count, time
    """

    def check(self):
        """ check SAT """
        raise NotImplementedError

    def add(self, *constraints):
        """ add constraints """
        raise NotImplementedError

    def bv(self, name, length=0):
        """ return a named bitvector or a new one
            if the name doesn't exist yet
        """
        raise NotImplementedError

    def true(self):
        """ return new boolean constant """
        raise NotImplementedError

    def false(self):
        """ return new boolean constant """
        raise NotImplementedError

    def bvconst(self, value, length):
        """ return new bv constant """
        raise NotImplementedError

    def bool(self, name):
        """ return new boolean """
        raise NotImplementedError

    def _bool(self, value):
        if value is True:
            return self.true()
        if value is False:
            return self.false()
        raise ValueError("_bool can only take bool, not {} ({})".format(value, type(value)))

    def _and(self, bv1, bv2):
        """ bitwise and """
        raise NotImplementedError

    def _or(self, bv1, bv2):
        """ bitwise or """
        raise NotImplementedError

    def _orb(self, b1, b2):
        """ boolean or """
        raise NotImplementedError

    def _xor(self, bv1, bv2):
        """ bitwise xor """
        raise NotImplementedError

    def _xorb(self, b1, b2):
        """ boolean xor """
        raise NotImplementedError

    def _eq(self, bv1, bv2):
        """ bitwise compare
            use _iff for booleans
        """
        raise NotImplementedError

    def _iff(self, b1, b2):
        """ if and only if """
        raise NotImplementedError

    def _not(self, bv):
        """ bitwise not """
        raise NotImplementedError

    def _if(self, cond, then, els):
        """ ternary conditional """
        raise NotImplementedError

    def _lshift(self, bv, i):
        """ left shift (drop upper bits, shift in 0s) """
        raise NotImplementedError

    def _rshift(self, bv, i):
        """ right shift (drop lower bits, shift in 0s) """
        raise NotImplementedError

    def _mult(self, bv1, bv2):
        """ unsigned multiplication """
        raise NotImplementedError

    def _mod(self, bv, mod):
        """ unsigned modulo """
        raise NotImplementedError

    def _ule(self, bv1, bv2):
        """ unsigned less than or equal """
        raise NotImplementedError

    def _uge(self, bv1, bv2):
        """ unsigned greater than or equal """
        raise NotImplementedError

    def _ult(self, bv1, bv2):
        """ unsigned less than """
        return self._not(self._uge(bv1, bv2))

    def _ugt(self, bv1, bv2):
        """ unsigned greater than """
        return self._not(self._ule(bv1, bv2))

    def push(self):
        """ push solver state """
        raise NotImplementedError

    def pop(self):
        """ pop solver state """
        raise NotImplementedError

    def model(self, *names):
        """ extract concrete values for bitvectors
            if multiple names, returns a dictionary {name: value}
            if one name, returns value
            raises ValueError for invalid names
        """
        raise NotImplementedError

    def assertions(self):
        """ extract assertions list """
        raise NotImplementedError

    def bvlen(self, name):
        """ get length of a bitvector """
        raise NotImplementedError

    def extract(self, bv, high, low):
        """ get sub-bitstring of a bitvector
            NOTE: [high, low] 0-indexed
            e.g.
            foo = solver.bv('foo', 32)
            bar = solver.extract(foo, 7, 0) # bottom 8 bits
            baz = solver.extract(foo, 31, 24) # top 8 bits
        """
        raise NotImplementedError

    def knownbits(self, name):
        """ get list of '0', '1', or '?' for bitvector
            lower bound on information about a bitvector
        """
        raise NotImplementedError

    def exact(self, name, print_model=True):
        """ exact count the current solver on the named bitvec """
        raise NotImplementedError

    def atleastx(self, name, x):
        """ Are there at least x solutions for name? """
        raise NotImplementedError

    def approxmc(self, tmpdir=gettempdir(), verbose=False, writeback=None):
        """ approxmc count the current solver """
        raise NotImplementedError

class Z3Solver(SolverInterface):
    """ Instantiate SolverInterface for z3 """

    def __init__(self):
        self.solver = z3.SolverFor("QF_BV")
        self.solver.set("cache_all", True)
        self.bitvecs = {}
        self.knownbitscache = {}
        self.knownbitsfresh = set()

    def unsat_core(self):
        return self.solver.unsat_core()

    def check(self):
        is_satisfiable = self.solver.check()
        if is_satisfiable == z3.sat:
            return True
        if is_satisfiable == z3.unsat:
            return False
        raise ValueError("Z3 Solver returned neither sat nor unsat: {}".format(is_satisfiable))

    def add(self, *constraints):
        self.knownbitsfresh = set() # empty the fresh cache list
        self.solver.add(*constraints)

    #def add_debug(self, constraint, name):
    #    self.knownbitsfresh = set() # empty the fresh cache list
    #    self.solver.assert_and_track(constraint, name)

    def bv(self, name, length=0):
        if name in self.bitvecs:
            return self.bitvecs[name]
        if length == 0:
            raise ValueError("New bitvecs must specify length")
        self.bitvecs[name] = z3.BitVec(name, length)
        return self.bitvecs[name]

    def bool(self, name):
        return z3.Bool(name)

    def true(self):
        return True

    def false(self):
        return False

    def bvconst(self, value, length):
        return z3.BitVecVal(value, length)

    def _udiv(self, bv1, bv2):
        return z3.UDiv(bv1, bv2)

    def _and(self, bv1, bv2):
        return bv1 & bv2

    def _andb(self, b1, b2):
        return z3.And(b1, b2)

    def _or(self, bv1, bv2):
        return bv1 | bv2

    def _orb(self, b1, b2):
        return z3.Or(b1, b2)

    def _xor(self, bv1, bv2):
        return bv1 ^ bv2

    def _xorb(self, b1, b2):
        return z3.Xor(b1, b2)

    def _eq(self, bv1, bv2):
        return bv1 == bv2

    def _iff(self, b1, b2):
        return b1 == b2

    def _not(self, bv):
        return z3.Not(bv)

    def _if(self, cond, then, els):
        return z3.If(cond, then, els)

    def _lshift(self, bv, i):
        return bv << i

    def _rshiftbv(self, bv, i):
        return bv >> i

    def _rshift(self, bv, i):
        return z3.LShR(bv, i)

    def _mult(self, bv1, bv2):
        return bv1 * bv2

    def _mod(self, bv, mod):
        return bv % mod

    def _div(self, bv1, bv2):
        return bv1 // bv2

    def _add(self, bv1, bv2):
        return bv1 + bv2

    def _sub(self, bv1, bv2):
        return bv1 - bv2

    def _ule(self, bv1, bv2):
        return z3.ULE(bv1, bv2)

    def _uge(self, bv1, bv2):
        return z3.UGE(bv1, bv2)

    def _ult(self, bv1, bv2):
        return self._not(self._uge(bv1, bv2))

    def _ugt(self, bv1, bv2):
        return self._not(self._ule(bv1, bv2))

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def assertions(self):
        return self.solver.assertions()

    def smt2(self):
        """ output constraints in SMTLIB2 format """
        return self.solver.to_smt2()

    def model(self, *names):
        try:
            m = self.solver.model()
        except z3.z3types.Z3Exception:
            self.check()
            m = self.solver.model()
        result = {}
        for n in names:
            try:
                result[n] = m[self.bv(n)]
            except ValueError as e:
                # This occurs when n was not the name of a solver variable
                # Intercept and re-raise to clarify error message
                raise ValueError("Variable '{}' not found".format(n)) from e
            if result[n] is None:
                result[n] = m.evaluate(self.bv(n), model_completion=True)
            result[n] = result[n].as_long()
        if len(names) == 1:
            return result[names[0]]
        return result

    def bvlen(self, name):
        return self.bitvecs[name].size()

    def cnf(self, add_true=False):
        """ Convert formula to CNF (represented as instance of class CNF) """
        self.check()
        goal = z3.Goal()
        goal.add(self.solver.assertions())
        tactic = z3.Then('simplify', 'propagate-values', 'bit-blast', 'tseitin-cnf')
        subgoal = tactic(goal)
        cnf = CNF()
        # Convert tseitin-cnf to cnf file string, internally in z3
        dimacs_str = subgoal[0].dimacs()
        # Use the CNF file to fill out the CNF object
        write_to_dict = dimacs_str.split('\n')
        for line in write_to_dict:
            if line !=  "":
                if line.startswith("c"): # read mapping for z3 to CNF vars
                    try:
                        _, cnf_var, z3_var = line.split(" ")
                    except ValueError as e:
                        print(line)
                        raise e
                    cnf.variables[z3_var] = cnf_var
                elif not line.startswith("p"): # it's a clause line
                    clause = line.split(" ")
                    cnf.clauses.append(clause[:-1])
                elif line.startswith("p"): # it's the header line
                    header_line = line.split(" ")
                    cnf.var = int(header_line[2])+1
        if add_true: # insert a variable which is simply asserted true
            true = cnf.newvar()
            cnf.variables["_true"] = str(true)
            cnf.clauses.append([str(true)])
        return cnf

    def knownbits(self, name):
        if name in self.knownbitscache:
            previous = self.knownbitscache[name]
        else:
            previous = []
        if name in self.knownbitsfresh:
            return previous
        _bv = self.bv(name)
        length = self.bvlen(name)
        soln = ['?']*length
        if not self.check():
            raise ValueError("Solver must be satisfiable")
        for i in range(length):
            if len(previous) != 0 and previous[i] != '?':
                soln[i] = previous[i]
                continue
            critical = False
            for guess in (0, 1):
                self.push()
                self.add(self._not(
                         self._eq(self.extract(_bv,i,i),
                                  self.bvconst(guess,1))))
                if not self.check():
                    critical = True
                    soln[i] = str(guess)
                    self.pop()
                    break
                self.pop()
            if not critical:
                soln[i] = '?'
        self.knownbitscache[name] = copy.copy(soln)
        self.knownbitsfresh.add(name)
        return soln

    def extract(self, bv, high, low):
        return z3.Extract(high, low, bv)

    def concat(self, *bvs):
        return z3.Concat(bvs)

    def extend(self, bv, n_zeroes):
        return z3.ZeroExt(n_zeroes,bv)

    def exact(self, name, print_model=False):
        count = 0
        self.push()
        while self.check():
            count += 1
            model = self.model(name)
            if print_model:
                print("Solution {}: {}".format(count, model))
            self.add(self._not(self._eq(self.bv(name),
                                        self.bvconst(model, self.bvlen(name)))))
        self.pop()
        return count

    def atleastx(self, name, x):
        count = 0
        self.push()
        while self.check() and count < x:
            count += 1
            model = self.model(name)
            self.add(self._not(self._eq(self.bv(name),
                                        self.bvconst(model, self.bvlen(name)))))
        self.pop()
        return count == x

    def approxmc(self, cnf=None, indep=[], tmpdir=gettempdir(), verbose=False, writeback=None):
        os.putenv("LD_LIBRARY_PATH", LOUVAIN_LIBS)
        with NamedTemporaryFile(mode='w+', dir=tmpdir) as f:
            if cnf is None:
                self.check()
                if verbose:
                    print("Generating CNF...")
                cnf_start = time.time()
                write_stream = str(self.cnf(add_true=False))
                cnf_duration = time.time() - cnf_start
                if verbose:
                    print("CNF generated in {}s".format(cnf_duration))
                    print("Writing CNF to {}".format(f.name))
            else:
                write_stream = str(cnf)
                cnf_duration = 0
            if indep:
                f.write("c ind {} 0\n".format(" ".join([str(x) for x in indep])))
            f.write(write_stream)
            f.seek(0)
            if not indep:
                try:
                    output = subprocess.check_output(
                            ['arjun', '--recomp', '1', f.name]).split(b"\n")
                    f.seek(0)
                except subprocess.CalledProcessError as e:
                    if verbose:
                        print("Arjun error")
                    raise e
                results = []
                appending = False
                for line in output:
                    if line.startswith(b"c ind"):
                        appending = True
                    if appending:
                        results.append(line)
                    else:
                        continue
                    if line.endswith(b" 0"):
                        break
                results = b" ".join(results)
                try:
                    indep = [int(x) for x in results.split(b" ")[2:-1]]
                except (IndexError, ValueError) as e:
                    print("Error parsing Arjun output")
                    raise e
                f.write("c ind {} 0\n".format(" ".join([str(x) for x in indep])))
                f.write(write_stream)
                f.seek(0)
            if writeback is not None:
                if verbose:
                    print("Writing back CNF to {}".format(writeback))
                os.system("cp {} {}".format(f.name, writeback))
                f.seek(0)
            if verbose:
                print("Running ApproxMC...")
            appmc_start = time.time()
            try:
                output = subprocess.check_output(['approxmc', f.name])
                f.seek(0)
                appmc_duration = time.time() - appmc_start
                last_line = output.split(b'\n')[-2] # one empty line after it
                # last item of last line
                count = int(last_line.split(b' ')[-1])
            except subprocess.CalledProcessError as e:
                if verbose:
                    print("ApproxMC error")
                    f.seek(0)
                    os.system("cp {} {}".format(f.name, "{}.appmc_error".format(f.name)))
                    print(e.output)
                raise e
            if verbose:
                print("ApproxMC finished in {}s".format(appmc_duration))
            return count, cnf_duration+appmc_duration
