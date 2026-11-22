module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataBu
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.DoubleCosetMeasures.StatementV

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

end Local

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

end Family

end Formalism.MainNotions.ZetaProductPairs

end
