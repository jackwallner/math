# Windmills of 4-cycles and a 2003 conjecture on α-labelings

**Status:** refutes Conjecture 3.10 of R. M. Figueroa-Centeno, R. Ichishima and F. A. Muntaner-Batle, "Labeling the vertex amalgamation of graphs", *Discuss. Math. Graph Theory* 23 (2003) 129-139, [doi:10.7151/dmgt.1190](https://doi.org/10.7151/dmgt.1190). Listed as open in Gallian's *Dynamic Survey of Graph Labeling* (2026 edition).

**The conjecture.** The one-point union of n copies of the cycle C_m admits an α-labeling if and only if mn ≡ 0 (mod 4).

**Theorem (proved, and verified in Lean 4).** The one-point union of n copies of C_4 has an α-labeling if and only if n ≤ 4. So the conjecture fails for m = 4 and every n ≥ 5.

**Computed.** The one-point union of 8 copies of C_6 (mn = 48) also has no α-labeling: two independent exact solvers (CP-SAT and a CNF model under a SAT solver) report none.

## Proof

An α-labeling of a bipartite graph with q edges is an injective f: V → {0, ..., q} whose edge differences |f(u) - f(v)| are exactly 1, ..., q, with a threshold λ such that every edge has one end labelled at most λ and the other above λ.

Let G be n copies of C_4 sharing a hub, q = 4n. Replacing f by q - f if needed, the hub is on the low side. Then the low side is the hub plus the n far vertices, the high side is the 2n neighbours of the hub, every high vertex is adjacent to the hub and to exactly one other low vertex, and every non-hub low vertex has degree 2. Let h be the hub's label and t the largest low label.

1. **t - h ≤ 2.** Suppose t - h ≥ 3. Difference 1 must join t to t + 1. Difference 2 is t to t + 2 or t - 1 to t + 1; the latter is impossible, because t + 1 already has its two neighbours t and h, and t - 1 ≠ h. Difference 3 is then t to t + 3 (impossible, t already has degree 2), t - 1 to t + 2, or t - 2 to t + 1 (impossible, both high vertices already have their two neighbours t and h, and neither t - 1 nor t - 2 is h). Contradiction.
2. **h ≤ 2.** Map each low label x to t - x and each high label y to q + t + 1 - y. Every difference d becomes q + 1 - d, so this is again an α-labeling with largest low label t (0 is always a label) and hub label t - h. Step 1 now gives h ≤ 2.
3. So all n + 1 low labels lie in {0, ..., 4}, and n ≤ 4.

Labelings for n ≤ 4 exist (their Theorem 3.8; explicit ones are in the Lean file `lean/Windmill/Existence.lean`).

## Check it

- **Lean:** `cd lean && lake build`. The main theorem `Windmill.alpha_iff_le_four` states the full "if and only if n ≤ 4" and depends only on Lean's standard axioms (propext, Classical.choice, Quot.sound). It is rebuilt by GitHub Actions on every push. The definitions a reader has to trust are in `lean/Windmill/Defs.lean`.
- **Paper:** `paper.pdf` (also on Zenodo).
