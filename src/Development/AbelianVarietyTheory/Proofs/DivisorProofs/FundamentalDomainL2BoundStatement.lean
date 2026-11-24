module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2Bound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.fundamental_domain_L2_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ, (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) → ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧ ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.QuotLocInt.integrableOn_compact | exact GlobalTheory.QuotLocInt.integrableOn_compact | (intros; apply GlobalTheory.QuotLocInt.integrableOn_compact <;> assumption)
