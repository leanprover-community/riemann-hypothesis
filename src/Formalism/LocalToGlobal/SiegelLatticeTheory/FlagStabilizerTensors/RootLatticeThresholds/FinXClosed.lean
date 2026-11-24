module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairTiesPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
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

namespace Formalism.L2.SG.Pf

theorem iotaRowC_holds : FinXP.IotaRowC := fun _ _ Y _ _ s₁ s₂ hr =>
  Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (congrArg (fun q => q.1.1) hr) (congrArg (fun q => q.2.1.1) hr)
    (congrArg (fun q => q.2.2) hr)

theorem pairTiesAll_holds : Formalism.L2.SG.TermTieOf.PairTiesAll := FinXP.pairTies_of iotaRowC_holds


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem finXC_of (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  FinXP.finX_holds hWu hRF Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

end Formalism.L2.SG.Pf
