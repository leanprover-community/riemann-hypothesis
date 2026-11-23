module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal : ∀ (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G), Measurable e → mK Kᶜ = 0 → (∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) → lam ≠ 0 → (∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤) → (∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧ ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) → ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f → ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  first | exact @GlobalTheory.Twist.lintegral_haar_eq_transversal | exact GlobalTheory.Twist.lintegral_haar_eq_transversal | (intros; apply GlobalTheory.Twist.lintegral_haar_eq_transversal <;> assumption)
