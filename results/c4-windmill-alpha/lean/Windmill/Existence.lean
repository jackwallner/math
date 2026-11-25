import Windmill.Defs

/-!
# Alpha-labelings for zero to four copies

`check` is a Boolean test of `IsAlphaLabeling` over explicit lists of all vertices and
edges, `check_sound` proves it implies `IsAlphaLabeling`, and `decide` runs it on the
labelings below (taken from the computer search; vertex order hub, then `a i, d i, b i`).
-/

namespace Windmill

def allV (n : Nat) : List (V n) :=
  .hub :: ((List.finRange n).map .a ++ (List.finRange n).map .d ++ (List.finRange n).map .b)

theorem mem_allV {n : Nat} (v : V n) : v ∈ allV n := by
  cases v <;> simp [allV, List.mem_finRange]

def allE (n : Nat) : List (Edge n) :=
  (List.finRange n).flatMap fun i => [.hubA i, .aD i, .dB i, .bHub i]

theorem mem_allE {n : Nat} (e : Edge n) : e ∈ allE n := by
  cases e <;> simp [allE, List.mem_finRange]

/-- A Boolean check of `IsAlphaLabeling n f` with threshold `lam`. -/
def check (n : Nat) (f : V n → Fin (4 * n + 1)) (lam : Nat) : Bool :=
  (allV n).all (fun u => (allV n).all fun v => f u != f v || u == v) &&
  (allE n).all (fun e => 1 ≤ edgeDiff f e && edgeDiff f e ≤ 4 * n) &&
  (List.range (4 * n + 1)).all (fun k => k == 0 || (allE n).any fun e => edgeDiff f e == k) &&
  (allE n).all (fun e => min (f e.ends.1).val (f e.ends.2).val ≤ lam &&
    lam < max (f e.ends.1).val (f e.ends.2).val)

theorem check_sound {n : Nat} {f : V n → Fin (4 * n + 1)} {lam : Nat}
    (h : check n f lam = true) : IsAlphaLabeling n f := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨hinj, hdiff⟩, hcov⟩, hthr⟩ := h
  refine ⟨?_, ?_, ?_, lam, ?_⟩
  · intro u v huv
    rcases hinj u (mem_allV u) v (mem_allV v) with h | h
    · exact absurd huv h
    · exact h
  · intro e; exact hdiff e (mem_allE e)
  · intro k hk1 hk2
    rcases hcov k (by omega) with h | ⟨e, -, he⟩
    · omega
    · exact ⟨e, he⟩
  · intro e; exact hthr e (mem_allE e)

/-- Labels from a hub value and a list of `(a i, d i, b i)` values, one per copy. -/
def mkLab (n hub : Nat) (copies : List (Nat × Nat × Nat)) : V n → Fin (4 * n + 1)
  | .hub => ⟨hub % (4 * n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .a i => ⟨(copies.getD i (0, 0, 0)).1 % (4 * n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .d i => ⟨(copies.getD i (0, 0, 0)).2.1 % (4 * n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .b i => ⟨(copies.getD i (0, 0, 0)).2.2 % (4 * n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem alpha0 : IsAlphaLabeling 0 (mkLab 0 0 []) :=
  check_sound (lam := 0) (by decide)

theorem alpha1 : IsAlphaLabeling 1 (mkLab 1 1 [(4, 0, 2)]) :=
  check_sound (lam := 1) (by decide)

theorem alpha2 : IsAlphaLabeling 2 (mkLab 2 0 [(3, 2, 4), (6, 1, 8)]) :=
  check_sound (lam := 2) (by decide)

theorem alpha3 : IsAlphaLabeling 3 (mkLab 3 1 [(4, 3, 5), (7, 2, 9), (10, 0, 12)]) :=
  check_sound (lam := 3) (by decide)

theorem alpha4 :
    IsAlphaLabeling 4 (mkLab 4 2 [(5, 4, 6), (15, 0, 16), (9, 1, 7), (14, 3, 12)]) :=
  check_sound (lam := 4) (by decide)

/-- For `n ≤ 4` the one-point union of `n` copies of `C4` has an alpha-labeling. -/
theorem alpha_of_le_four (n : Nat) (hn : n ≤ 4) :
    ∃ f : V n → Fin (4 * n + 1), IsAlphaLabeling n f := by
  match n, hn with
  | 0, _ => exact ⟨_, alpha0⟩
  | 1, _ => exact ⟨_, alpha1⟩
  | 2, _ => exact ⟨_, alpha2⟩
  | 3, _ => exact ⟨_, alpha3⟩
  | 4, _ => exact ⟨_, alpha4⟩

end Windmill
