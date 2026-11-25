"""Print the LaTeX rows for the note's tables from labelings/*.json and ../results-*.log."""
import json
import pathlib
import re
from collections import defaultdict

HERE = pathlib.Path(__file__).parent
SHOW = ["C4x1", "C4x2", "C4x3", "C4x4", "K21x2", "K23x6", "K24x8"]


def name(fam: str, a: int, n: int) -> str:
    if fam == "C":
        return f"$C_{{{a}}}^{{({n})}}$"
    return f"$K_{{2,{a}}}^{{\\langle {n}\\rangle}}$"


def copies(rec: dict) -> str:
    f, a, n = rec["labels"], rec["a"], rec["n"]
    parts = []
    for i in range(n):
        if rec["family"] == "C":
            base = 1 + i * (a - 1)
            parts.append("(" + ",".join(str(f[base + j]) for j in range(a - 1)) + ")")
        else:
            base = 1 + i * (a + 1)
            parts.append(f"{f[base]}:" + ",".join(str(f[base + 1 + j]) for j in range(a)))
    return "; ".join(parts)


def labeling_rows() -> None:
    for tag in SHOW:
        rec = json.loads((HERE / "labelings" / f"{tag}.json").read_text())
        q = len(rec["edges"])
        print(f"{name(rec['family'], rec['a'], rec['n'])} & {q} & {rec['labels'][0]} & {copies(rec)} \\\\")


def search_rows() -> None:
    yes, no = defaultdict(set), defaultdict(set)
    open_ = defaultdict(set)
    pat = re.compile(r"^(C|K2)(\d+)x(\d+) (?:low=\w+ (\w+)|cnf (\w+))")
    for log in sorted(HERE.parent.glob("results-*.log")):
        for line in log.read_text().splitlines():
            m = pat.match(line)
            if not m:
                continue
            key, n = (m.group(1), int(m.group(2))), int(m.group(3))
            st = m.group(4) or m.group(5)
            if st in ("OPTIMAL", "FEASIBLE") or st.startswith("SAT"):
                yes[key].add(n)
            elif st in ("INFEASIBLE", "UNSAT"):
                no[key].add(n)
            else:
                open_[key].add(n)
    for key in sorted(set(yes) | set(no) | set(open_), key=lambda k: (k[0] != "C", k[1])):
        fam, a = key
        g = f"$C_{{{a}}}^{{(n)}}$" if fam == "C" else f"$K_{{2,{a}}}^{{\\langle n\\rangle}}$"
        fmt = lambda s: f"${', '.join(map(str, sorted(s)))}$" if s else "--"
        und = open_[key] - yes[key] - no[key]
        extra = f" ({fmt(und)} undecided)" if und else ""
        print(f"{g} & {fmt(yes[key])} & {fmt(no[key])}{extra} \\\\")


if __name__ == "__main__":
    labeling_rows()
    print("%%")
    search_rows()
