module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι), (∀ c : ℂ, IsFam act 0 fun _ _ => c) ∧ (∀ w f g, IsFam act w f → IsFam act w g → (IsFam act w fun i τ => f i τ + g i τ) ∧ IsFam act w fun i τ => f i τ - g i τ) ∧ (∀ w (c : ℂ) f, IsFam act w f → IsFam act w fun i τ => c * f i τ) ∧ (∀ w w' f g, IsFam act w f → IsFam act w' g → IsFam act (w + w') fun i τ => f i τ * g i τ) ∧ (∀ w f (k : ℕ), IsFam act w f → IsFam act (k * w) fun i τ => f i τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act w (f k)) → IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ), (∀ k ∈ t, IsFam act (w k) (f k)) → IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧ (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f, (∀ k γ, φ (act' k γ) = act (φ k) γ) → IsFam act w f → IsFam act' w fun k => f (φ k)) := by
  first | exact @GlobalTheory.QFam.isFam_algebra | exact GlobalTheory.QFam.isFam_algebra | (intros; apply GlobalTheory.QFam.isFam_algebra <;> assumption)
