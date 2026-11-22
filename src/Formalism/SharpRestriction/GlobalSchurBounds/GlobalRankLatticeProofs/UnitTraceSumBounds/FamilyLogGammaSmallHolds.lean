module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.DesignExistsOfChoices

@[expose] public section

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dite_eq_left h]

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

instance instUltraCp (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

end Nu

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions

end Formalism.MainNotions.ShortIntervalPrimes
