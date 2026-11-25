"""Search for an alpha-valuation of a one-point union with OR-tools CP-SAT.

Usage: search_cpsat.py FAMILY A N [--low centre|other|both] [--time SEC] [--workers W]
  FAMILY C  : n copies of C_A sharing one vertex
  FAMILY K2 : n copies of K_{2,A} glued at a degree-A vertex

An alpha-valuation is an injective f: V -> {0..q} whose edge differences are
exactly {1..q}, with a threshold lam such that every edge has one end <= lam
and the other > lam. For a connected bipartite graph that forces one colour
class (the "low" class) below lam. Complementing f -> q - f swaps the classes,
so --low centre alone already decides existence; --low both runs both anyway.

No symmetry breaking is used, so an INFEASIBLE answer is a plain proof of
nonexistence by the solver. A labeling found is written to
labelings/<FAMILY><A>x<N>.json for check_labeling.py.
"""
import argparse
import json
import pathlib

from ortools.sat.python import cp_model

from graphs import build, two_colour

OUT = pathlib.Path(__file__).parent / "labelings"


def solve(family: str, a: int, n: int, low: int, tmax: float, workers: int):
    nv, edges = build(family, a, n)
    side = two_colour(nv, edges)
    q = len(edges)
    md = cp_model.CpModel()
    f = [md.NewIntVar(0, q, f"f{v}") for v in range(nv)]
    md.AddAllDifferent(f)
    lam = md.NewIntVar(0, q, "lam")
    for v in range(nv):
        if side[v] == low:
            md.Add(f[v] <= lam)
        else:
            md.Add(f[v] >= lam + 1)
    diffs = []
    for u, v in edges:
        lo, hi = (u, v) if side[u] == low else (v, u)
        e = md.NewIntVar(1, q, "")
        md.Add(e == f[hi] - f[lo])
        diffs.append(e)
    md.AddAllDifferent(diffs)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = tmax
    s.parameters.num_workers = workers
    r = s.Solve(md)
    labels = [s.Value(x) for x in f] if r in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return s.StatusName(r), labels, s.WallTime()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("family", choices=["C", "K2"])
    ap.add_argument("a", type=int)
    ap.add_argument("n", type=int)
    ap.add_argument("--low", choices=["centre", "other", "both"], default="centre")
    ap.add_argument("--time", type=float, default=600)
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()
    lows = {"centre": [0], "other": [1], "both": [0, 1]}[args.low]
    for low in lows:
        status, labels, wall = solve(args.family, args.a, args.n, low, args.time, args.workers)
        tag = f"{args.family}{args.a}x{args.n}"
        print(f"{tag} low={'centre' if low == 0 else 'other'} {status} {wall:.1f}s", flush=True)
        if labels is not None:
            OUT.mkdir(exist_ok=True)
            nv, edges = build(args.family, args.a, args.n)
            rec = {"family": args.family, "a": args.a, "n": args.n,
                   "edges": edges, "labels": labels, "solver": "cp-sat",
                   "low_class": "centre" if low == 0 else "other"}
            (OUT / f"{tag}.json").write_text(json.dumps(rec))
            break


if __name__ == "__main__":
    main()
