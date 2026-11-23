module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingTermUniqueSupportedBalancedCone
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

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.leadingTerm_unique_supported_balancedCone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ (β : LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), 0 < k → (∀ j, 0 < c j) → k • β = ∑ j, c j • γ j → (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[O] X) (N : ℕ), 3 ≤ N → (∀ x, CongMod N (e x) x) → d * φ.evalZ β = (∑ i, β (e (a i)) (e (a i)) : ℤ) → ∀ x, e x = x := by
  first | exact @GlobalTheory.Poinc.leadingTerm_unique | exact GlobalTheory.Poinc.leadingTerm_unique | (intros; apply GlobalTheory.Poinc.leadingTerm_unique <;> assumption)
