module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqP
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

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  first | (exact @GlobalTheory.annihilator_lift_of_mul_eq_p) | (exact GlobalTheory.annihilator_lift_of_mul_eq_p) | (intros; apply GlobalTheory.annihilator_lift_of_mul_eq_p  <;> assumption)
