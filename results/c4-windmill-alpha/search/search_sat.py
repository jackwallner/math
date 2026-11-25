"""Second, independent nonexistence check: a pure CNF encoding under CaDiCaL.

Usage: search_sat.py FAMILY A N
Graph is rebuilt here without graphs.py. The low class is the class of the
shared vertex (enough by complementation). Variables x[v][l] mean f(v) = l,
y[e][d] mean edge e gets difference d. Low vertices take labels 0..lam and
high ones lam+1..q; the threshold lam is enumerated outside the solver, so
each run is a set of plain SAT calls. Prints UNSAT only if every lam is UNSAT.
"""
import sys

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def graph(family: str, a: int, n: int):
    edges, low = [], {0}
    nv = 1
    for _ in range(n):
        if family == "C":
            path = list(range(nv, nv + a - 1))
            nv += a - 1
            ring = [0] + path
            edges += [(ring[i], ring[(i + 1) % a]) for i in range(a)]
            low |= set(path[1::2])
        else:
            d, xs = nv, list(range(nv + 1, nv + 1 + a))
            nv += a + 1
            low.add(d)
            edges += [(0, x) for x in xs] + [(d, x) for x in xs]
    return nv, edges, low


def feasible(nv, edges, low, lam):
    q = len(edges)
    pool = IDPool()
    rng = {v: range(0, lam + 1) if v in low else range(lam + 1, q + 1) for v in range(nv)}
    x = {(v, l): pool.id(("x", v, l)) for v in range(nv) for l in rng[v]}
    cnf = []

    def exactly_one(lits):
        cnf.extend(CardEnc.equals(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses)

    def at_most_one(lits):
        if len(lits) > 1:
            cnf.extend(CardEnc.atmost(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses)

    for v in range(nv):
        exactly_one([x[v, l] for l in rng[v]])
    for l in range(q + 1):
        at_most_one([x[v, l] for v in range(nv) if (v, l) in x])
    by_diff = {d: [] for d in range(1, q + 1)}
    for i, (u, v) in enumerate(edges):
        lo, hi = (u, v) if u in low else (v, u)
        ys = {}
        for d in range(1, q + 1):
            y = pool.id(("y", i, d))
            ys[d] = y
            by_diff[d].append(y)
            pairs = [(a, a + d) for a in rng[lo] if a + d in rng[hi]]
            # y -> OR of (x_lo=a & x_hi=a+d); since lo, hi take one label each,
            # it is enough: y & x_lo=a -> x_hi=a+d, and y -> lo in feasible a's.
            cnf.append([-y] + [x[lo, a] for a, _ in pairs])
            for a in rng[lo]:
                if a + d in rng[hi]:
                    cnf.append([-y, -x[lo, a], x[hi, a + d]])
        exactly_one(list(ys.values()))
        # also tie the difference down from the labels side
        for a in rng[lo]:
            for b in rng[hi]:
                if b - a >= 1:
                    cnf.append([-x[lo, a], -x[hi, b], ys[b - a]])
    for d in range(1, q + 1):
        exactly_one(by_diff[d])
    with Solver(name="cadical153", bootstrap_with=cnf) as s:
        return s.solve()


def main() -> None:
    family, a, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    nv, edges, low = graph(family, a, n)
    found = [lam for lam in range(len(low) - 1, len(edges) - (nv - len(low)) + 1)
             if feasible(nv, edges, low, lam)]
    tag = f"{family}{a}x{n}"
    print(f"{tag} cnf {'SAT lam=' + str(found) if found else 'UNSAT'}", flush=True)


if __name__ == "__main__":
    main()
