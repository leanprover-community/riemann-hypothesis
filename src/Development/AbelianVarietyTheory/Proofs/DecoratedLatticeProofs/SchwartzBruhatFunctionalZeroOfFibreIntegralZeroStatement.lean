module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatFunctionalZeroOfFibreIntegralZero
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero | exact GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero | (intros; apply GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero <;> assumption)
