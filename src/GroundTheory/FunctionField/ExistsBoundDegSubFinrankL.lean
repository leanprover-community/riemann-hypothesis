module

public import Mathlib
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.FunctionField.PlaceBasic
public import GroundTheory.FunctionField.Divisor
public import GroundTheory.FunctionField.DivisorDegree

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

theorem deg_sub_finrank_L_mono {D E : Divisor k K} (h : D ≤ E) :
    deg D - (finrank k (L D) : ℤ) ≤ deg E - finrank k (L E) := by
  have := finrank_L_le_of_le h
  linarith

theorem exists_bound_deg_sub_finrank_L :
    ∃ γ : ℤ, ∀ D : Divisor k K, deg D - (finrank k (L D) : ℤ) ≤ γ := by
  classical
  obtain ⟨x, hx, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  set F := IntermediateField.adjoin k {x} with hF
  set n := finrank F K with hn
  let b := Module.finBasis F K
  set B : Divisor k K := poleDivisor x with hBdef
  set C : Divisor k K := ∑ j, poleDivisor (b j) with hCdef
  have hB : 0 ≤ B := poleDivisor_nonneg x
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => poleDivisor_nonneg _
  have hCj : ∀ j, (poleDivisor (b j) : Divisor k K) ≤ C := fun j =>
    Finset.single_le_sum (f := fun j => (poleDivisor (b j) : Divisor k K))
      (fun j _ => poleDivisor_nonneg _) (Finset.mem_univ j)
  have key : ∀ l : ℕ, ((l + 1 : ℤ) * n) ≤ finrank k (L (l • B + C)) := by
    intro l
    set D : Divisor k K := l • B + C with hD'
    have hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * b p.2 ∈ L D := by
      rintro ⟨i, j⟩ v
      rw [map_mul, map_pow]
      have hx' := valuation_le_exp_poleDivisor x v
      have hb' := (valuation_le_exp_poleDivisor (b j) v).trans
        (WithZero.exp_le_exp.2 (Finsupp.le_def.1 (hCj j) v))
      have hBv : 0 ≤ B v := by simpa using Finsupp.le_def.1 hB v
      have hil : ((i : ℕ) : ℤ) ≤ l := by exact_mod_cast Nat.lt_succ_iff.1 i.2
      calc v.valuation x ^ (i : ℕ) * v.valuation (b j)
          ≤ WithZero.exp (B v) ^ (i : ℕ) * WithZero.exp (C v) :=
            mul_le_mul' (pow_le_pow_left' hx' _) hb'
        _ ≤ WithZero.exp (D v) := by
            rw [← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp]
            simp only [hD', Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
            have := mul_le_mul_of_nonneg_right hil hBv
            linarith
    let G : Fin (l + 1) × Fin n → L D := fun p => ⟨x ^ (p.1 : ℕ) * b p.2, hmem p⟩
    have hli : LinearIndependent k G := by
      apply LinearIndependent.of_comp (L D).subtype
      have hb' : LinearIndependent k fun i : Fin (l + 1) =>
          (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ) := by
        apply LinearIndependent.of_comp F.val.toLinearMap
        have h := linearIndependent_pow_of_transcendental hx (l + 1)
        have heq : (F.val.toLinearMap ∘ fun i : Fin (l + 1) =>
            (IntermediateField.AdjoinSimple.gen k x) ^ (i : ℕ)) =
            fun i : Fin (l + 1) => x ^ (i : ℕ) := by
          funext i
          simp
        rw [heq]
        exact h
      convert linearIndependent_smul hb' b.linearIndependent using 1
      funext p
      simp [G, Algebra.smul_def]
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    have : ((l + 1 : ℕ) * n : ℕ) ≤ (finrank k (L D) : ℤ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have hdegB : deg B = n := deg_poleDivisor hx
  have hn1 : 0 < n := Module.finrank_pos
  refine ⟨deg C - n, fun D => ?_⟩
  set A₁ : Divisor k K := D ⊔ 0 with hA₁def
  have hA₁ : 0 ≤ A₁ := le_sup_right
  have h1 := deg_sub_finrank_L_mono (le_sup_left : D ≤ A₁)
  set l := (deg A₁).toNat with hldef
  have hl : (l : ℤ) = deg A₁ := Int.toNat_of_nonneg (deg_nonneg hA₁)
  set El : Divisor k K := l • B + C with hEl
  have hdegEl : deg El = l * n + deg C := by
    rw [hEl, map_add (f := _), map_nsmul, hdegB, nsmul_eq_mul]
  have hkey := key l
  have hle : El - A₁ ≤ El := sub_le_self _ hA₁
  have h2 := finrank_L_le_of_le hle
  rw [map_sub] at h2
  have hpos : 0 < finrank k (L (El - A₁)) := by
    have hn1' : (1 : ℤ) ≤ n := by exact_mod_cast hn1
    have : ((l : ℤ) + 1) * 1 ≤ ((l : ℤ) + 1) * n := mul_le_mul_of_nonneg_left hn1' (by positivity)
    have : (0 : ℤ) < finrank k (L (El - A₁)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  set D₁ : Divisor k K := A₁ + divisor (z : K)⁻¹ with hD₁
  have hD₁El : D₁ ≤ El := by
    rw [hD₁, divisor_inv, ← sub_eq_add_neg, ← sub_nonneg]
    have : El - (A₁ - divisor (z : K)) = divisor (z : K) + (El - A₁) := by abel
    rw [this]
    exact hzL
  have hlD₁ : finrank k (L D₁) = finrank k (L A₁) := finrank_L_add_divisor A₁ (inv_ne_zero hz0)
  have hdegD₁ : deg D₁ = deg A₁ := by rw [hD₁, map_add (f := _), deg_divisor, add_zero]
  have h3 := deg_sub_finrank_L_mono hD₁El
  rw [hlD₁, hdegD₁] at h3
  linarith

end Divisor

open Divisor

namespace Divisor

instance finiteDimensional_quotient (D : Divisor k K) :
    FiniteDimensional k (Repartition k K ⧸ (A D ⊔ principal k K)) := by
  obtain ⟨E, hE⟩ := exists_eq_genusInt (k := k) (K := K)
  have h := relSpace_sup_eq_top D hE
  have := finiteDimensional_relSpace_of_le (le_sup_left : D ≤ D ⊔ E)
  rw [h] at this
  exact Module.Finite.equiv Submodule.topEquiv

end Divisor

end GroundTheory.FunctionField
