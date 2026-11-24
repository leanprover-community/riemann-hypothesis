module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.EFinal
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocQuad1GHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

theorem stepIntG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyFinal.BM.stepIntG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem stepConvG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.S.Pv.ConvG.StepConvG :=
  Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem realObj_inInfinityX_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) {D : Formalism.BasicNotions.D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : Formalism.L2.SG.RealObj.InInfinityX X u u' sc :=
  Formalism.L2.SG.Pf.realObj_inInfinityX_ofG (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepIntG_jsz hJ) (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_jsz hJ) hg X u u' sc hsc

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
