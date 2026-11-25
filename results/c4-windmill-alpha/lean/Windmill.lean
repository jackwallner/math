import Windmill.Defs
import Windmill.Core
import Windmill.Existence
import Windmill.Nonexistence

/-!
# Main theorem

The one-point union of `n` copies of `C4` has an alpha-labeling if and only if `n ≤ 4`.
This refutes Conjecture 3.10 of Figueroa-Centeno, Ichishima and Muntaner-Batle
(Discuss. Math. Graph Theory 23 (2003)) for `m = 4` and every `n ≥ 5`.
-/

namespace Windmill

theorem alpha_iff_le_four (n : Nat) :
    (∃ f : V n → Fin (4 * n + 1), IsAlphaLabeling n f) ↔ n ≤ 4 := by
  constructor
  · rintro ⟨f, hf⟩
    exact le_four_of_alpha hf
  · exact alpha_of_le_four n

end Windmill

#print axioms Windmill.alpha_iff_le_four
#print axioms Windmill.no_alpha_of_five_le
