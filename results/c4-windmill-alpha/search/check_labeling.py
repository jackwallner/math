"""Independent checker for saved alpha-valuations.

Usage: check_labeling.py [labelings/*.json ...]
Rebuilds each graph from (family, a, n) with its own code, confirms the saved
edge list is that graph up to vertex names, then checks the alpha conditions
directly from the definition. Uses nothing from the search scripts.
"""
import json
import pathlib
import sys


def rebuild(family: str, a: int, n: int) -> set[frozenset]:
    out, nxt = set(), 1
    for _ in range(n):
        if family == "C":
            ring = [0] + list(range(nxt, nxt + a - 1))
            nxt += a - 1
            out |= {frozenset((ring[i], ring[(i + 1) % a])) for i in range(a)}
        else:
            d = nxt
            nxt += a + 1
            for x in range(d + 1, d + 1 + a):
                out |= {frozenset((0, x)), frozenset((d, x))}
    return out


def check(path: pathlib.Path) -> str:
    rec = json.loads(path.read_text())
    fam, a, n = rec["family"], rec["a"], rec["n"]
    f = rec["labels"]
    edges = [tuple(e) for e in rec["edges"]]
    assert {frozenset(e) for e in edges} == rebuild(fam, a, n), "edge list mismatch"
    q = len(edges)
    assert q == (a * n if fam == "C" else 2 * a * n)
    nv = 1 + n * ((a - 1) if fam == "C" else (a + 1))
    assert len(f) == nv
    assert len(set(f)) == nv, "labels not distinct"
    assert all(0 <= x <= q for x in f), "label out of range"
    diffs = sorted(abs(f[u] - f[v]) for u, v in edges)
    assert diffs == list(range(1, q + 1)), "not graceful"
    # alpha: some lam with min(edge) <= lam < max(edge) for every edge
    lo = max(min(f[u], f[v]) for u, v in edges)
    hi = min(max(f[u], f[v]) for u, v in edges)
    assert lo < hi, "no threshold"
    return f"{path.name}: OK  q={q}  lam in [{lo},{hi - 1}]  centre={f[0]}"


def main() -> None:
    paths = [pathlib.Path(p) for p in sys.argv[1:]] or sorted(
        (pathlib.Path(__file__).parent / "labelings").glob("*.json"))
    for p in paths:
        print(check(p))


if __name__ == "__main__":
    main()
