""" sugarbeets.py """
import random
from math import log2, ceil
from functools import reduce

#NUM_PLAYERS = 1200

#PRICE_BITS = 9
#UNITS_BITS = 15

NUM_PLAYERS = 6
HONEST_BUYERS = 2
HONEST_SELLERS = 2
ADV_BUYERS = 1
ADV_SELLERS = 1

PRICE_BITS = 3
UNITS_BITS = 2
UNITS_MASK = (1 << UNITS_BITS)-1
SUM_BITS = ceil(log2(NUM_PLAYERS))+UNITS_BITS

TARGET_LEN = (HONEST_BUYERS+HONEST_SELLERS)*UNITS_BITS*(pow(2, PRICE_BITS)-1) # bit length of unknown target input
CHOSEN_LEN = (ADV_BUYERS+ADV_SELLERS)*UNITS_BITS*(pow(2, PRICE_BITS)-1) # bit length of input adversary (this program) controls
OUTCOME_LEN = PRICE_BITS # bit length of the longest variable in OUTCOMES
USE_LEAKAGE = False

def encode_secret(buys, sells):
    secret = 0
    shift = 0
    for buyer in buys:
        for units in buyer:
            secret |= (units << shift)
            shift += UNITS_BITS
    for seller in sells:
        for units in seller:
            secret |= (units << shift)
            shift += UNITS_BITS
    return secret

SECRET_BUYS = [sorted([random.randint(0, pow(2, UNITS_BITS)-1) for _ in range(1, pow(2, PRICE_BITS))], reverse=True) for _ in range(HONEST_BUYERS)]
SECRET_SELLS =[sorted([random.randint(0, pow(2, UNITS_BITS)-1) for _ in range(1, pow(2, PRICE_BITS))]) for _ in range(HONEST_SELLERS)]
SECRET = encode_secret(SECRET_BUYS, SECRET_SELLS)

def unpack(solver, aai):
    return (solver.extract(aai, SUM_BITS+PRICE_BITS-1, PRICE_BITS),
            solver.extract(aai, PRICE_BITS-1, 0))

def _min(solver, aai, bbi):
    a, _ = unpack(solver, aai)
    b, _ = unpack(solver, bbi)
    return solver._if(solver._ule(a, b), aai, bbi)

def abs_sub(solver, a, b):
    return solver._if(solver._uge(a, b), a - b, b - a)

def compute_deltas(solver, chosen, target):
    mt = solver.atleastx("target", 2)
    demands = [solver.bvconst(0, SUM_BITS) for _ in range(1, pow(2, PRICE_BITS))]
    supplies = [solver.bvconst(0, SUM_BITS) for _ in range(1, pow(2, PRICE_BITS))]
    honest_offset = 0
    adv_offset = 0
    for _ in range(HONEST_BUYERS):
        for price in range(1, pow(2, PRICE_BITS)):
            demands[price-1] = (demands[price-1] +
                    solver.extend(solver.extract(target,
                                   UNITS_BITS-1+honest_offset,
                                   honest_offset), SUM_BITS-UNITS_BITS))
            honest_offset += UNITS_BITS
    for _ in range(ADV_BUYERS):
        for price in range(1, pow(2, PRICE_BITS)):
            demands[price-1] = (demands[price-1] +
                                solver.extend(
                                  solver.extract(chosen,
                                   UNITS_BITS-1+adv_offset,
                                   adv_offset), SUM_BITS-UNITS_BITS))
            adv_offset += UNITS_BITS
    """
    if not mt:
        solver.push()
        _vars = [solver.bv("test{}".format(i), SUM_BITS) for i in range(1, pow(2, PRICE_BITS))]
        for _var, demand in zip(_vars, demands):
            solver.add(solver._eq(_var, demand))
        solver.check()
        print("Solver demand:")
        print([solver.model('test{}'.format(i)) for i in range(1, pow(2, PRICE_BITS))])
        solver.pop()
    """
    for _ in range(HONEST_SELLERS):
        for price in range(1, pow(2, PRICE_BITS)):
            supplies[price-1] = (supplies[price-1] +
                                 solver.extend(
                                  solver.extract(target,
                                   UNITS_BITS-1+honest_offset,
                                   honest_offset), SUM_BITS-UNITS_BITS))
            honest_offset += UNITS_BITS
    for _ in range(ADV_SELLERS):
        for price in range(1, pow(2, PRICE_BITS)):
            supplies[price-1] = (supplies[price-1] +
                                 solver.extend(
                                  solver.extract(chosen,
                                   UNITS_BITS-1+adv_offset,
                                   adv_offset), SUM_BITS-UNITS_BITS))
            adv_offset += UNITS_BITS
    """
    if not mt:
        solver.push()
        _vars = [solver.bv("test{}".format(i), SUM_BITS) for i in range(1, pow(2, PRICE_BITS))]
        for _var, supply in zip(_vars, supplies):
            solver.add(solver._eq(_var, supply))
        solver.check()
        print("Solver supply:")
        print([solver.model('test{}'.format(i)) for i in range(1, pow(2, PRICE_BITS))])
        solver.pop()
    """
    deltas = [abs_sub(solver, d, s) for d, s in zip(demands, supplies)]
    """
    if not mt:
        solver.push()
        _vars = [solver.bv("test{}".format(i), SUM_BITS) for i in range(1, pow(2, PRICE_BITS))]
        for _var, delta in zip(_vars, deltas):
            solver.add(solver._eq(_var, delta))
        solver.check()
        print("Solver deltas:")
        print([solver.model('test{}'.format(i)) for i in range(1, pow(2, PRICE_BITS))])
        solver.pop()
    """
    return deltas

def func_smt(solver, chosen_input, target_input):
    prices = list(range(1, pow(2, PRICE_BITS)))
    deltas = compute_deltas(solver, chosen_input, target_input)
    __min = lambda a, b: _min(solver, a, b)
    mcp_min = reduce(__min,
            [solver.concat(deltas[price-1], solver.bvconst(price, PRICE_BITS))
             for price in prices])
    _, mcpi = unpack(solver, mcp_min)
    return mcpi

def func(chosen_input, target_input):
    buys = []
    sells = []
    for _ in range(HONEST_BUYERS):
        buy = []
        for _ in range(1, pow(2, PRICE_BITS)):
            buy.append(target_input & UNITS_MASK)
            target_input >>= UNITS_BITS
        buys.append(buy)
    for _ in range(HONEST_SELLERS):
        sell = []
        for _ in range(1, pow(2, PRICE_BITS)):
            sell.append(target_input & UNITS_MASK)
            target_input >>= UNITS_BITS
        sells.append(sell)
    for _ in range(ADV_BUYERS):
        buy = []
        for _ in range(1, pow(2, PRICE_BITS)):
            buy.append(chosen_input & UNITS_MASK)
            chosen_input >>= UNITS_BITS
        buys.append(buy)
    for _ in range(ADV_SELLERS):
        sell = []
        for _ in range(1, pow(2, PRICE_BITS)):
            sell.append(chosen_input & UNITS_MASK)
            chosen_input >>= UNITS_BITS
        sells.append(sell)
    demands = []
    supplies = []
    for price in range(1, pow(2, PRICE_BITS)):
        demands.append(sum([buy[price-1] for buy in buys]))
        supplies.append(sum([sell[price-1] for sell in sells]))
    deltas = [abs(d - s) for d, s in zip(demands, supplies)]
    mcp_delta = min(deltas)
    mcp_min = deltas.index(mcp_delta)+1
    return mcp_min
