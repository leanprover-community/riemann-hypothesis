import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_unit_norm_eq_of_algHom : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] (ψ : A →ₐ[K] K) (c : K), c ≠ 0 → ∃ y : Aˣ, Algebra.norm K (y : A) = c := by
  intro K A _ _ _ _ _ ψ c hc
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker ψ)
  have he0 : ψ e = 0 := by
    have : e ∈ RingHom.ker ψ := by rw [hI]; exact Ideal.subset_span rfl
    exact this
  set f : A := 1 - e with hf
  have hψf : ψ f = 1 := by simp [hf, he0]
  have hmul : ∀ a : A, f * a = ψ a • f := by
    intro a
    have h1 : a - algebraMap K A (ψ a) ∈ RingHom.ker ψ := by
      simp [RingHom.mem_ker]
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have h2 : f * (b * e) = 0 := by
      have : e * e = e := he
      rw [hf]; linear_combination (-b) * this
    rw [hb, mul_sub, sub_eq_zero] at h2
    rw [h2, Algebra.smul_def, mul_comm]
  have hff : f * f = f := by rw [hmul, hψf, one_smul]
  have hinv : (1 + (c - 1) • f) * (1 + (c⁻¹ - 1) • f) = 1 := by
    have : (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0 := by field_simp; ring
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, hff]
    simp only [one_mul, mul_one]
    rw [add_assoc, ← add_smul, ← add_smul]
    have h3 : c - 1 + (c⁻¹ - 1 + (c - 1) * (c⁻¹ - 1)) = 0 := by linear_combination this
    rw [h3]; simp
  refine ⟨⟨1 + (c - 1) • f, 1 + (c⁻¹ - 1) • f, hinv, by rw [mul_comm, hinv]⟩, ?_⟩
  rw [Algebra.norm_apply]
  have hT : LinearMap.mul K A (1 + (c - 1) • f) = LinearMap.transvection ψ.toLinearMap ((c - 1) • f) := by
    ext a
    simp [LinearMap.transvection.apply, hmul, smul_smul, mul_comm]
  change LinearMap.det (LinearMap.mul K A (1 + (c - 1) • f)) = c
  rw [hT, LinearMap.transvection.det]
  simp [hψf]

end GlobalTheory.CNorm
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem kNorm_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  intro p F L _ _ _ φ δ r hp hδ hr
  have hφ : φ δ ≠ 0 := (map_ne_zero φ).2 hδ
  have hsep : (X ^ p - C (φ δ) : L[X]).Separable :=
    separable_X_pow_sub_C (φ δ) (Nat.cast_ne_zero.2 hp.ne') hφ
  have hm : (X ^ p - C (φ δ) : L[X]).Monic := monic_X_pow_sub_C _ hp.ne'
  have : IsReduced (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  have : Module.Finite L (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (AdjoinRoot.powerBasis' hm).finite
  let ψ : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →ₐ[L] L :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id L L) r (by simp [hr])
  rw [eq_top_iff]
  intro x _
  rw [mem_kNorm]
  exact GlobalTheory.CNorm.exists_unit_norm_eq_of_algHom L _ ψ (φ (x : F)) ((map_ne_zero φ).2 x.ne_zero)

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  atlas_forward_decl GlobalTheory.CNorm.kNorm_eq_top_of_pow
end
