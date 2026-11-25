# Lean proof: the C4 windmill has an alpha-labeling exactly when n <= 4

A kernel-checked Lean 4 proof that the one-point union of `n` copies of the 4-cycle
has an alpha-valuation if and only if `n <= 4`. This refutes Conjecture 3.10 of
Figueroa-Centeno, Ichishima and Muntaner-Batle (Discuss. Math. Graph Theory 23 (2003)
129-139) for `m = 4` and every `n >= 5`.

## The statement

```lean
theorem Windmill.alpha_iff_le_four (n : Nat) :
    (∃ f : V n → Fin (4 * n + 1), IsAlphaLabeling n f) ↔ n ≤ 4
```

In words: for every natural number `n`, the graph below has an alpha-labeling if and
only if `n <= 4`. The definitions it rests on are in `Windmill/Defs.lean` (about 50
lines); that file is all a reader has to check by eye.

- **Graph.** Vertices are a hub and, for each copy `i < n`, three vertices `a i`, `d i`,
  `b i`. Edges are `hub-a i`, `a i-d i`, `d i-b i`, `b i-hub`, so there are `q = 4n` edges.
- **Alpha-labeling** (Rosa's alpha-valuation). A map `f` from vertices to `{0, ..., q}` such that
  1. `f` is injective;
  2. every edge difference `|f u - f v|` lies in `{1, ..., q}`;
  3. every number in `{1, ..., q}` is the difference of some edge;
  4. some threshold `lam` has `min (f u) (f v) <= lam < max (f u) (f v)` on every edge `uv`.

Conditions 2 and 3 together say that the set of edge differences is exactly `{1, ..., q}`.

`Windmill.no_alpha_of_five_le` states the counterexample direction on its own:
`5 ≤ n → ¬ ∃ f, IsAlphaLabeling n f`.

## The proof

- `Windmill/Existence.lean`: explicit labelings for `n = 0, ..., 4`, checked by `decide`
  through a Boolean checker that is proved sound (`check_sound`).
- `Windmill/Core.lean`: the arithmetic. With the hub on the low side (label `c`), the
  differences 1, 2, 3 force `lam <= c + 2`, and the differences `q`, `q-1`, `q-2` force
  `c <= 2`. So each `f(d i)` lies in `{c-2, c-1, c+1, c+2}`, and the `f(d i)` are
  distinct, so `n <= 4`.
- `Windmill/Nonexistence.lean`: the graph layer. The threshold puts the hub and all `d i`
  on one side. If the hub is high, the labeling `x ↦ q - x` keeps every edge difference
  and puts the hub low.

## Axioms

```
'Windmill.alpha_iff_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Windmill.no_alpha_of_five_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. There is no `sorry`, no custom axiom and no
`native_decide`.

## Versions

- Lean 4.36.0 (`leanprover/lean4:v4.36.0`, commit 611c117b), pinned in `lean-toolchain`.
- No Mathlib or other dependency: the proof uses only Lean core (`omega`, `decide`).
  The trusted base is therefore just the Lean kernel and the definitions file.

## Build

Install Lean with [elan](https://github.com/leanprover/elan), then from this folder:

```bash
lake build
```

A clean build takes about 2 minutes on an M-series Mac and prints the axiom lines above.
