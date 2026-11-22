module

public import Mathlib
public import Formalism.DoubleCosetMeasures.StatementV
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Proved

open Formalism.BasicNotions.TH

end Proved

section Split20

set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Split20

end Formalism.MainNotions.DIV

end
