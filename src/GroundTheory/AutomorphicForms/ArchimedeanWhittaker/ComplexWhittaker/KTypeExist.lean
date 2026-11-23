module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.IsClosedDivisorComponent
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.PeterWeyl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace KT

open Matrix MeasureTheory Complex Finset
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep GL2C H)

theorem psi_mul_mul (n : ℕ) (q : ℤ) (l₁ k l₂ : U2) :
    psi n q n (l₁ * k * l₂) = (((l₁ * k * l₂ : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n *
      ((k : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q *
        (((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * ((l₂ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q) := by
  simp only [psi, Nat.sub_self, pow_zero, mul_one]
  rw [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.mul_val, Matrix.det_mul, Matrix.det_mul,
    mul_zpow, mul_zpow]
  ring

theorem eq_zero_of_forall_Q_eq_zero (hQ : ∀ (n : ℕ) (q : ℤ) (y : H), Q σ n q n y = 0) (v : H) :
    v = 0 := by
  set g : U2 → ℂ := fun k => ⟪σ (kC k) v, v⟫_ℂ with hg
  have hgc : Continuous g := (continuous_orbit_K σ v).inner continuous_const
  have hint : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2),
      ∫ k, conj (psi n q n k) * ⟪σ (kC l₁) v, σ (kC k) (σ (kC l₂)⁻¹ v)⟫_ℂ ∂μK = 0 := by
    intro n q l₁ l₂
    rw [← inner_Kint_right σ (continuous_conj_psi n q n)]
    exact (congrArg _ (hQ n q _)).trans (inner_zero_right _)
  have hg0 : g = 0 := by
    refine PW.eq_zero_of_forall_integral_coeff hgc fun n q l₁ l₂ => ?_
    have h1 := hint n q l₁ l₂
    rw [← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂] at h1
    have hne : (((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * ((l₂ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q)
        ≠ 0 := mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 l₁)) (zpow_ne_zero _ (det_ne_zero_of_U2 l₂))
    have h2 : conj (∫ k, conj (psi n q n (l₁ * (k * l₂))) *
        ⟪σ (kC l₁) v, σ (kC (l₁ * (k * l₂))) (σ (kC l₂)⁻¹ v)⟫_ℂ ∂μK) = 0 := by
      rw [h1, map_zero]
    rw [← integral_conj] at h2
    have e : ∀ k : U2, conj (conj (psi n q n (l₁ * (k * l₂))) *
        ⟪σ (kC l₁) v, σ (kC (l₁ * (k * l₂))) (σ (kC l₂)⁻¹ v)⟫_ℂ) =
        ((((l₁ * k * l₂ : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n *
          ((k : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * g k) *
        (((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * ((l₂ : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q) := by
      intro k
      have hσ : σ (kC (l₁ * k * l₂)) (σ (kC l₂)⁻¹ v) = σ (kC l₁) (σ (kC k) v) := by
        rw [map_mul, map_mul, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply,
          ← UnitaryRep.map_mul_apply σ (kC l₂) (kC l₂)⁻¹, mul_inv_cancel,
          UnitaryRep.map_one, ContinuousLinearMap.one_apply]
      rw [← mul_assoc l₁ k l₂, map_mul (starRingEnd ℂ), starRingEnd_self_apply, inner_conj_symm,
        psi_mul_mul, hσ, UnitaryRep.inner_map_left, ← UnitaryRep.map_mul_apply, inv_mul_cancel,
        UnitaryRep.map_one, ContinuousLinearMap.one_apply, hg]
      ring
    simp_rw [e] at h2
    rw [integral_mul_const] at h2
    exact (mul_eq_zero.1 h2).resolve_right hne
  have h1 : g 1 = 0 := by rw [hg0]; rfl
  simp only [hg, map_one, UnitaryRep.map_one, ContinuousLinearMap.one_apply] at h1
  exact inner_self_eq_zero.1 h1

end KT

end GroundTheory.Automorphic.ArchWhittakerC
