module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocQuad1GHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.RealObj.EnergyConvJ


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem threeDimData_inputs_of_besselMapUniq (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs :=
  Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem stepIntG_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyFinal.stepIntG_holds (threeDimData_inputs_of_besselMapUniq hJ)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem stepConvG_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.L2.S.Pv.ConvG.StepConvG :=
  stepConvG_holds (threeDimData_inputs_of_besselMapUniq hJ)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem realObj_inInfinityX_jsz (hJ : PI.BesselMapUniq.BesselMapUniq) {D : Formalism.BasicNotions.D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : Formalism.L2.SG.RealObj.InInfinityX X u u' sc :=
  Formalism.L2.SG.Pf.realObj_inInfinityX_ofG (stepIntG_jsz hJ) (stepConvG_jsz hJ) hg X u u' sc hsc

end Formalism.L2.SG.RealObj.EnergyConvJ
