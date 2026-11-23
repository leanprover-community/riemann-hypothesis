module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

theorem _root_.GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  first | exact @GlobalTheory.PerFix.exists_fixed_near | exact GlobalTheory.PerFix.exists_fixed_near | (intros; apply GlobalTheory.PerFix.exists_fixed_near <;> assumption)
