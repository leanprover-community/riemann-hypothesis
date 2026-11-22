module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.InnerProductFormulaField

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Loc

variable {D : D7} (X : Loc D) (Z : DivX D)

end Loc

variable (D : D7) (Z : DivX D) (T : ThetaX D) (A : TH.ProvA) (X : Loc D)

section RealConstant

variable {D} {T}

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

end RealConstant

section Level

variable {D} {T} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

variable (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (V : LevObj T S)

end Level

attribute [instance] LevDat.nacg LevDat.ips LevDat.fd

section Fam

variable {eps : ℝ}

end Fam

end Formalism.MainNotions.InnerProductFormulaField

end
