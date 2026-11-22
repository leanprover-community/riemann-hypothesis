module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

end Derived

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

attribute [instance] Loc4.instCHr

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
