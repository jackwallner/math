/-!
# The arithmetic heart of the nonexistence proof

Numbers only, no graphs. The hub label is `c`. Copy `i` has label `D i` on `d i` and
labels `H i true`, `H i false` on `a i`, `b i`. The hub and every `d i` are in the low
class (at most `lam`); every `a i`, `b i` is in the high class (above `lam`, at most `q`).
The edge differences of copy `i` are `H i s - c` and `H i s - D i`.

* `lam ≤ c + 2`: otherwise the differences 1, 2, 3 cannot all occur.
* `c ≤ 2`: otherwise the differences `q`, `q - 1`, `q - 2` cannot all occur.

So every `D i` is one of `c - 2, c - 1, c + 1, c + 2`. The `D i` are distinct, so `n ≤ 4`.
-/

namespace Windmill

private theorem bool_third : ∀ s t u : Bool, s ≠ t → u = s ∨ u = t := by decide

section
variable (n q c lam : Nat) (H : Fin n → Bool → Nat) (D : Fin n → Nat)

/-- If `lam ≥ c + 3`, the edge differences 1, 2, 3 cannot all occur. -/
theorem lam_le (hD : ∀ i, D i ≤ lam) (hH : ∀ i s, lam < H i s)
    (hHinj : ∀ i s j t, H i s = H j t → i = j ∧ s = t)
    (hDinj : ∀ i j, D i = D j → i = j) (hq : 3 ≤ q)
    (cover : ∀ k, 1 ≤ k → k ≤ q → ∃ i s, H i s = c + k ∨ H i s = D i + k) :
    lam ≤ c + 2 := by
  refine Nat.le_of_not_lt fun h => ?_
  -- Difference 1 is `H r s - D r` with `D r = lam`, `H r s = lam + 1`.
  obtain ⟨r, s, hr⟩ := cover 1 (by omega) (by omega)
  have := hH r s; have := hD r
  have hr' : D r = lam ∧ H r s = lam + 1 := by omega
  -- Difference 2 is `H r t - D r` with `t ≠ s` and `H r t = lam + 2`.
  obtain ⟨j, t, hj⟩ := cover 2 (by omega) (by omega)
  have := hH j t; have := hD j
  have hj' : (H j t = lam + 1 ∧ D j + 1 = lam) ∨ (H j t = lam + 2 ∧ D j = lam) := by omega
  rcases hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rfl, -⟩ := hHinj j t r s (by omega); omega
  obtain rfl := hDinj j r (by omega)
  have hts : s ≠ t := fun e => by subst e; omega
  -- Difference 3 has nowhere to go.
  obtain ⟨m, u, hm⟩ := cover 3 (by omega) (by omega)
  have := hH m u; have := hD m
  have hm' : H m u = lam + 1 ∨ H m u = lam + 2 ∨ (H m u = lam + 3 ∧ D m = lam) := by omega
  rcases hm' with h1 | h1 | ⟨h1, h2⟩
  · obtain ⟨rfl, -⟩ := hHinj m u j s (by omega); omega
  · obtain ⟨rfl, -⟩ := hHinj m u j t (by omega); omega
  · obtain rfl := hDinj m j (by omega)
    rcases bool_third s t u hts with rfl | rfl <;> omega

/-- If `c ≥ 3`, the edge differences `q`, `q - 1`, `q - 2` cannot all occur. -/
theorem c_le (hH : ∀ i s, H i s ≤ q)
    (hHinj : ∀ i s j t, H i s = H j t → i = j ∧ s = t)
    (hDinj : ∀ i j, D i = D j → i = j) (hq : 3 ≤ q)
    (cover : ∀ k, 1 ≤ k → k ≤ q → ∃ i s, H i s = c + k ∨ H i s = D i + k) :
    c ≤ 2 := by
  refine Nat.le_of_not_lt fun h => ?_
  -- Difference `q` is `H r s - D r` with `D r = 0`, `H r s = q`.
  obtain ⟨r, s, hr⟩ := cover q (by omega) (by omega)
  have := hH r s
  have hr' : D r = 0 ∧ H r s = q := by omega
  -- Difference `q - 1` is `H r t - D r` with `t ≠ s` and `H r t = q - 1`.
  obtain ⟨j, t, hj⟩ := cover (q - 1) (by omega) (by omega)
  have := hH j t
  have hj' : (H j t = q ∧ D j = 1) ∨ (H j t + 1 = q ∧ D j = 0) := by omega
  rcases hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨rfl, -⟩ := hHinj j t r s (by omega); omega
  obtain rfl := hDinj j r (by omega)
  have hts : s ≠ t := fun e => by subst e; omega
  -- Difference `q - 2` has nowhere to go.
  obtain ⟨m, u, hm⟩ := cover (q - 2) (by omega) (by omega)
  have := hH m u
  have hm' : H m u = q ∨ H m u + 1 = q ∨ (H m u + 2 = q ∧ D m = 0) := by omega
  rcases hm' with h1 | h1 | ⟨h1, h2⟩
  · obtain ⟨rfl, -⟩ := hHinj m u j s (by omega); omega
  · obtain ⟨rfl, -⟩ := hHinj m u j t (by omega); omega
  · obtain rfl := hDinj m j (by omega)
    rcases bool_third s t u hts with rfl | rfl <;> omega

/-- The arithmetic core: with the hub in the low class, there are at most 4 copies. -/
theorem core (hq : q = 4 * n)
    (hc : c ≤ lam) (hD : ∀ i, D i ≤ lam) (hH : ∀ i s, lam < H i s ∧ H i s ≤ q)
    (hHinj : ∀ i s j t, H i s = H j t → i = j ∧ s = t)
    (hDinj : ∀ i j, D i = D j → i = j) (hDc : ∀ i, D i ≠ c)
    (cover : ∀ k, 1 ≤ k → k ≤ q → ∃ i s, H i s = c + k ∨ H i s = D i + k) :
    n ≤ 4 := by
  refine Nat.le_of_not_lt fun hn => ?_
  have up := lam_le n q c lam H D hD (fun i s => (hH i s).1) hHinj hDinj (by omega) cover
  have low := c_le n q c H D (fun i s => (hH i s).2) hHinj hDinj (by omega) cover
  -- Five distinct values `D 0, ..., D 4` in `{c - 2, c - 1, c + 1, c + 2}`: impossible.
  have ne : ∀ x y : Fin n, x.val ≠ y.val → D x ≠ D y := fun x y hxy h =>
    hxy (congrArg Fin.val (hDinj x y h))
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let i4 : Fin n := ⟨4, by omega⟩
  have := ne i0 i1 (by show 0 ≠ 1; omega); have := ne i0 i2 (by show 0 ≠ 2; omega); have := ne i0 i3 (by show 0 ≠ 3; omega)
  have := ne i0 i4 (by show 0 ≠ 4; omega); have := ne i1 i2 (by show 1 ≠ 2; omega); have := ne i1 i3 (by show 1 ≠ 3; omega)
  have := ne i1 i4 (by show 1 ≠ 4; omega); have := ne i2 i3 (by show 2 ≠ 3; omega); have := ne i2 i4 (by show 2 ≠ 4; omega)
  have := ne i3 i4 (by show 3 ≠ 4; omega)
  have := hDc i0; have := hDc i1; have := hDc i2; have := hDc i3; have := hDc i4
  have := hD i0; have := hD i1; have := hD i2; have := hD i3; have := hD i4
  omega

end
end Windmill
