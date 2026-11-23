module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
