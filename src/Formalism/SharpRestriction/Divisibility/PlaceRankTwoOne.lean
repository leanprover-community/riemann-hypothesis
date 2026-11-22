module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.placeRankTwoOne

open Formalism.BasicNotions NumberField IsDedekindDomain

def NN (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

variable (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : Loc D X)

def dimY : ℕ := D.R.f * (D.R.r.choose 2)

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : LocF Fm)

end Fam

end Formalism.MainNotions.placeRankTwoOne

end
