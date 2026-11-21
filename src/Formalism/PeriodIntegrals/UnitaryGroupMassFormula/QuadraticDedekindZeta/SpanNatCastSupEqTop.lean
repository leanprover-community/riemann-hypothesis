import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂



variable {K : Type} [Field K] [NumberField K]


theorem cnt_one : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩




end PI.ClassNumImQ.ZetaNonvanishing₂
