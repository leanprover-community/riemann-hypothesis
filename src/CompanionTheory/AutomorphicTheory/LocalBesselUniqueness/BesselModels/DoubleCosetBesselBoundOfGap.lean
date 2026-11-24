module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

namespace BM

end BM

end Formalism.MainNotions.BridgeCS3d

namespace Formalism.MainNotions.BridgeCS3dBOW

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

theorem besselOfW_gap (hJ : CompanionTheory.Lime.BM.UniqGap) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := CompanionTheory.Lime.BM.dDFormOne hJ CompanionTheory.Lime.BM.inputs
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩

end Formalism.MainNotions.BridgeCS3dBOW
