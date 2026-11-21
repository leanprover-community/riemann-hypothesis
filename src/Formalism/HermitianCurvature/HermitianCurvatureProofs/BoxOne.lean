import Formalism.HermitianCurvature.Statement
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

namespace Formalism.FourierDecayAlt.P.BoxOne

open NumberField Finset


variable {E : Type} [Field E] [NumberField E]

theorem term_le (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (Kx : ℝ) (hK : 0 ≤ Kx) (l : E)
    (hl0 : l ≠ 0) :
    ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, ((1 / 2 : ℝ) ^ Kx) ^ (Nat.log 2 ⌊w l / x w⌋₊) := by
  apply Finset.prod_le_prod (fun w _ => le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (hx w).le (by positivity)) _))
  intro w _
  have hpos : 0 < x w / w l := div_pos (hx w) (InfinitePlace.pos_iff.2 hl0)
  rw [Formalism.SA.P.min_one_rpow _ _ hpos hK, ← Formalism.SA.P.pow_rpow_comm (1 / 2 : ℝ) Kx (by norm_num)]
  apply Real.rpow_le_rpow (le_min zero_le_one hpos.le) _ hK
  have hu : 0 < w l / x w := div_pos (InfinitePlace.pos_iff.2 hl0) (hx w)
  have := Formalism.SA.P.min_one_inv_le (w l / x w) hu
  rwa [one_div_div] at this

end Formalism.FourierDecayAlt.P.BoxOne

namespace Formalism.FourierDecayAlt.P

open NumberField Finset


end Formalism.FourierDecayAlt.P
