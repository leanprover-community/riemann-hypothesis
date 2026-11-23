module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruentTupleUnimodularImageOrLarge
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.congruent_tuple_unimodular_image_or_large : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (X₀ : Type) [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] [Module.Projective O X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (ι : Type) [Fintype ι] (a : ι → X₀), Submodule.span ℤ (Set.range a) = ⊤ → ∀ K : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ (k : X₀ →ₗ[ℤ] X) (μ : ι → X), IsUnimodMod O N k → (∀ i, CongMod N (μ i) (k (a i))) → (∃ e : X₀ ≃ₗ[O] X, ∀ i, e (a i) = μ i) ∨ K * lam ≤ (∑ i, β (μ i) (μ i) : ℤ) := by
  first | exact @GlobalTheory.Poinc.dichotomy | exact GlobalTheory.Poinc.dichotomy | (intros; apply GlobalTheory.Poinc.dichotomy <;> assumption)
