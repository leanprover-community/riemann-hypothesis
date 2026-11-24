module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
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
import Mathlib.RingTheory.WittVector.IsPoly
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

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
