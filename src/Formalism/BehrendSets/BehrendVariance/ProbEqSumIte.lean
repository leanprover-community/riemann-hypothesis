import Mathlib
import Formalism.BehrendSets.Statement

open Finset

noncomputable section

namespace Formalism.BehrendSets.Rand

variable {α : Type} [DecidableEq α]



theorem wt_nonneg (X T : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 0 ≤ wt X δ T := by
  unfold wt
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)










end Formalism.BehrendSets.Rand

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Rand

end Formalism.BehrendSets
