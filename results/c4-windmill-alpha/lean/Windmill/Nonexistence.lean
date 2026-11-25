import Windmill.Defs
import Windmill.Core

/-!
# No alpha-labeling for five or more copies

Every edge has one end at most `lam` and the other above it, so the hub and all `d i`
are on one side and all `a i`, `b i` on the other. If the hub is on the low side,
`core` applies directly. Otherwise replace every label `x` by `q - x`: edge differences
are unchanged and the sides swap, so `core` applies again.
-/

namespace Windmill

/-- The high vertices of copy `i`: `a i` for `true`, `b i` for `false`. -/
def hi {n : Nat} (i : Fin n) : Bool → V n
  | true => .a i
  | false => .b i

/-- The graph version of `core`, for a labeling with the hub on the low side. -/
theorem le_four_of_low_hub (n lam : Nat) (L : V n → Nat)
    (inj : ∀ u v, L u = L v → u = v) (hle : ∀ v, L v ≤ 4 * n)
    (cover : ∀ k, 1 ≤ k → k ≤ 4 * n →
      ∃ e : Edge n, Int.natAbs ((L e.ends.1 : Int) - L e.ends.2) = k)
    (hhub : L .hub ≤ lam) (hd : ∀ i, L (.d i) ≤ lam)
    (ha : ∀ i, lam < L (.a i)) (hb : ∀ i, lam < L (.b i)) :
    n ≤ 4 := by
  have hH : ∀ i s, lam < L (hi i s) ∧ L (hi i s) ≤ 4 * n := by
    intro i s
    cases s
    · exact ⟨hb i, hle _⟩
    · exact ⟨ha i, hle _⟩
  refine core n (4 * n) (L .hub) lam (fun i s => L (hi i s)) (fun i => L (.d i))
    rfl hhub hd hH ?_ ?_ ?_ ?_
  · intro i s j t h
    have h' := inj _ _ h
    cases s <;> cases t <;> simp only [hi] at h' <;> cases h' <;> exact ⟨rfl, rfl⟩
  · intro i j h
    cases inj _ _ h
    rfl
  · intro i h
    cases inj _ _ h
  · intro k hk1 hk2
    obtain ⟨e, he⟩ := cover k hk1 hk2
    cases e with
    | hubA i =>
      have := ha i
      simp only [Edge.ends] at he
      exact ⟨i, true, Or.inl (by simp only [hi]; omega)⟩
    | aD i =>
      have := ha i; have := hd i
      simp only [Edge.ends] at he
      exact ⟨i, true, Or.inr (by simp only [hi]; omega)⟩
    | dB i =>
      have := hb i; have := hd i
      simp only [Edge.ends] at he
      exact ⟨i, false, Or.inr (by simp only [hi]; omega)⟩
    | bHub i =>
      have := hb i
      simp only [Edge.ends] at he
      exact ⟨i, false, Or.inl (by simp only [hi]; omega)⟩

/-- Any alpha-labeling of the one-point union of `n` copies of `C4` has `n ≤ 4`. -/
theorem le_four_of_alpha {n : Nat} {f : V n → Fin (4 * n + 1)}
    (hf : IsAlphaLabeling n f) : n ≤ 4 := by
  obtain ⟨inj, -, cover, lam, thr⟩ := hf
  have injL : ∀ u v, (f u).val = (f v).val → u = v := fun u v h => inj u v (Fin.ext h)
  have hle : ∀ v, (f v).val ≤ 4 * n := fun v => Nat.le_of_lt_succ (f v).isLt
  have tA := fun i => thr (.hubA i)
  have tD := fun i => thr (.aD i)
  have tB := fun i => thr (.bHub i)
  simp only [Edge.ends] at tA tD tB
  by_cases hc : (f .hub).val ≤ lam
  · refine le_four_of_low_hub n lam (fun v => (f v).val) injL hle cover hc ?_ ?_ ?_
    · intro i; have := tA i; have := tD i; omega
    · intro i; have := tA i; omega
    · intro i; have := tB i; omega
  · -- The hub is high: use the complementary labeling `x ↦ q - x`.
    have hlq : lam < 4 * n := by have := hle .hub; omega
    refine le_four_of_low_hub n (4 * n - 1 - lam) (fun v => 4 * n - (f v).val)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro u v h
      have := hle u; have := hle v
      exact injL u v (by omega)
    · intro v; omega
    · intro k hk1 hk2
      obtain ⟨e, he⟩ := cover k hk1 hk2
      refine ⟨e, ?_⟩
      have := hle e.ends.1; have := hle e.ends.2
      simp only [edgeDiff] at he
      omega
    · omega
    · intro i; have := tA i; have := tD i; omega
    · intro i; have := tA i; omega
    · intro i; have := tB i; omega

/-- For `n ≥ 5` the one-point union of `n` copies of `C4` has no alpha-labeling. -/
theorem no_alpha_of_five_le (n : Nat) (hn : 5 ≤ n) :
    ¬ ∃ f : V n → Fin (4 * n + 1), IsAlphaLabeling n f := by
  rintro ⟨f, hf⟩
  have := le_four_of_alpha hf
  omega

end Windmill
