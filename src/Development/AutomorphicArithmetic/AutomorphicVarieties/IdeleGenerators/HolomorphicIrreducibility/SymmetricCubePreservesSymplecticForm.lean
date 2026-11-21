import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private noncomputable def s3F {S : Type} [CommRing S] (t d : S) : S[X] :=
  X ^ 4 + C (-(t ^ 3 - 2 * t * d)) * X ^ 3 + C (2 * d ^ 3 + (t ^ 3 - 3 * t * d) * d * t) * X ^ 2 +
    C (-(d ^ 3 * (t ^ 3 - 2 * t * d))) * X ^ 1 + C (d ^ 6) * X ^ 0

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1



omit [IsUltrametricDist K] in
private theorem Rl.neg {x y : K} (h : Rl x y) : Rl (-x) (-y) := by
  refine ⟨by simpa using h.1, ?_⟩
  rw [show -x - -y = -(x - y) by ring, norm_neg]
  exact h.2





end Rel

end UpperTheory.V.Sd
