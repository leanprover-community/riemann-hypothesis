import Mathlib
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

open Module PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_ne_top_of_smul {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    (x : O) (hx : x ≠ 0) (h : ∀ m : M, x • m = 0) : Module.length O M ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hI : ∀ i : Fin n, Ideal.span {x} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O M (f (Pi.single i 1))) := by
    intro i
    rw [Ideal.span_le]
    rintro _ rfl
    simp [h]
  let g : (Fin n → O ⧸ Ideal.span {x}) →ₗ[O] M :=
    ∑ i, ((Ideal.span {x}).liftQ _ (hI i)) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro m
    obtain ⟨v, rfl⟩ := hf m
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]; rfl
  have h1 : Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hx))
  have h2 := Module.length_le_of_surjective g hg
  rw [Module.length_pi] at h2
  intro htop
  rw [htop, top_le_iff] at h2
  rcases WithTop.mul_eq_top_iff.mp h2 with h3 | h3
  · exact h1 h3.2
  · have := ENat.card_eq_top.mp h3.1
    exact not_finite (Fin n)

def satL {O R : Type} [CommRing O] [AddCommGroup R] [Module O R] (l : O) (R' : Submodule O R) : Submodule O R where
  carrier := {z | ∃ t : ℕ, l ^ t • z ∈ R'}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, ?_⟩
    rw [smul_add, pow_add]
    refine R'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact R'.smul_mem _ hs
    · rw [mul_smul]; exact R'.smul_mem _ ht
  smul_mem' := by
    rintro c z ⟨t, ht⟩
    exact ⟨t, by rw [smul_comm]; exact R'.smul_mem c ht⟩

theorem dvd_pow_of_ne_zero (l : O) (hl : l ∈ IsLocalRing.maximalIdeal O) {r : O} (hr : r ≠ 0) :
    ∃ n : ℕ, r ∣ l ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hd : ϖ ∣ l := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hl
    exact hl
  exact ⟨n, Units.mul_left_dvd.mpr (pow_dvd_pow_of_dvd hd n)⟩


variable {R : Type} [AddCommGroup R] [Module O R]

abbrev Aq (O : Type) [CommRing O] (k : ℕ) := PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k}

abbrev Aql (O : Type) [CommRing O] (k c : ℕ) (l : O) :=
  PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)}

theorem spanX_le (k c : ℕ) (l : O) :
    Ideal.span {(X : PowerSeries O) ^ k} ≤ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)} :=
  Ideal.span_mono (by simp)

def red (k c : ℕ) (l : O) : Aq O k →ₐ[O] Aql O k c l := Ideal.Quotient.factorₐ O (spanX_le k c l)

theorem red_mk (k c : ℕ) (l : O) (a : PowerSeries O) :
    red k c l (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl


theorem smul_Aq (k : ℕ) (a : O) (y : Aq O k) :
    a • y = Ideal.Quotient.mk _ (C a) * y := by
  rw [Algebra.smul_def]; rfl


theorem red_eq_zero (k c : ℕ) (l : O) (y : Aq O k) (h : red k c l y = 0) :
    ∃ z : Aq O k, y = (l ^ c) • z := by
  induction y using Quotient.inductionOn' with | h a => ?_
  have h' : (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)})) a = 0 := h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair] at h'
  obtain ⟨u, w, huw⟩ := h'
  refine ⟨Ideal.Quotient.mk _ w, ?_⟩
  rw [smul_Aq]
  change Ideal.Quotient.mk _ a = _
  rw [← huw, ← map_mul, mul_comm (C (l ^ c)) w, Ideal.Quotient.eq, add_sub_cancel_right]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

section Main

variable [Module.Free O R] [Module.Finite O R]


end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount
