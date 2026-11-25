/-!
# The statement a reader has to trust

`V n` and `Edge n` describe the one-point union of `n` copies of the 4-cycle `C4`:
a shared vertex `hub`, and for each copy `i` three vertices `a i`, `d i`, `b i`
on the cycle `hub - a i - d i - b i - hub`. It has `q = 4 * n` edges.

`IsAlphaLabeling n f` is Rosa's alpha-valuation: `f` labels the vertices
injectively with numbers in `{0, ..., q}`, the edge differences `|f u - f v|`
form exactly the set `{1, ..., q}`, and some threshold `lam` has
`min (f u) (f v) ≤ lam < max (f u) (f v)` on every edge `uv`.
-/

namespace Windmill

/-- Vertices: the hub, plus `a i`, `d i`, `b i` for each copy `i < n`. -/
inductive V (n : Nat) where
  | hub : V n
  | a : Fin n → V n
  | d : Fin n → V n
  | b : Fin n → V n
  deriving DecidableEq

/-- Edges: `hub-a i`, `a i-d i`, `d i-b i`, `b i-hub` for each copy `i < n`. -/
inductive Edge (n : Nat) where
  | hubA : Fin n → Edge n
  | aD : Fin n → Edge n
  | dB : Fin n → Edge n
  | bHub : Fin n → Edge n

/-- The two endpoints of an edge. -/
def Edge.ends {n : Nat} : Edge n → V n × V n
  | .hubA i => (.hub, .a i)
  | .aD i => (.a i, .d i)
  | .dB i => (.d i, .b i)
  | .bHub i => (.b i, .hub)

/-- The label difference `|f u - f v|` on an edge `uv`. -/
def edgeDiff {n : Nat} (f : V n → Fin (4 * n + 1)) (e : Edge n) : Nat :=
  Int.natAbs (((f e.ends.1).val : Int) - (f e.ends.2).val)

/-- An alpha-labeling of the one-point union of `n` copies of `C4` (`q = 4 * n`). -/
def IsAlphaLabeling (n : Nat) (f : V n → Fin (4 * n + 1)) : Prop :=
  -- `f` is injective
  (∀ u v : V n, f u = f v → u = v) ∧
  -- every edge difference lies in `{1, ..., q}`
  (∀ e : Edge n, 1 ≤ edgeDiff f e ∧ edgeDiff f e ≤ 4 * n) ∧
  -- every number in `{1, ..., q}` is an edge difference
  (∀ k : Nat, 1 ≤ k → k ≤ 4 * n → ∃ e : Edge n, edgeDiff f e = k) ∧
  -- a threshold separates the two ends of every edge
  (∃ lam : Nat, ∀ e : Edge n,
    min (f e.ends.1).val (f e.ends.2).val ≤ lam ∧ lam < max (f e.ends.1).val (f e.ends.2).val)

end Windmill
