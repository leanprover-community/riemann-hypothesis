import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)

theorem isUA_mul {g h : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hh : IsUA c G h) :
    IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) : IsUA c G g⁻¹ :=
  ⟨isUnit_nonsing_inv_det g hg.1, fun x y => by
    rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]⟩

theorem IsKM_maps {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  have : k *ᵥ x = M • y + x := by rw [← e]; abel
  rw [this]
  exact add_mem (nsmul_mem hy M) hx

theorem isKM_mul {k h : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hh : IsKM c G L M h) :
    IsKM c G L M (k * h) := by
  refine ⟨isUA_mul c G hk.1 hh.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hk.2.1 _ (IsKM_maps c G L M hh hx)
    obtain ⟨z, hz, e'⟩ := hh.2.1 x hx
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hh.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have hi : ∀ z, k⁻¹ *ᵥ (k *ᵥ z) = z := fun z => by
    rw [mulVec_mulVec, nonsing_inv_mul k hk.1.1, one_mulVec]
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ⟨k *ᵥ x, IsKM_maps c G L M hk hx, hi x⟩⟩
  obtain ⟨z, hz, e⟩ := hk.2.2 x hx
  obtain ⟨y, hy, e'⟩ := hk.2.1 z hz
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [← e, hi, smul_neg, ← e']; abel


theorem ratM_mul (a b : Matrix (Fin n) (Fin n) E) : ratM F (a * b) = ratM F a * ratM F b :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E))

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl


theorem uEquiv_trans {a b d : Matrix (Fin n) (Fin n) (RA F E)} (h : UEquiv c G L M a b)
    (h' : UEquiv c G L M b d) : UEquiv c G L M a d := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', rfl⟩ := h'
  exact ⟨γ' * γ, by rw [ratM_mul]; exact isUA_mul c G hγ' hγ, k * k', isKM_mul c G L M hk hk', by
    rw [ratM_mul]; simp only [Matrix.mul_assoc]⟩





theorem one_tmul_injective : Function.Injective fun x : E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by
  have hA : Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
    haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨0, 1, fun h => by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
      exact zero_ne_one (α := v.adicCompletion F) this⟩
    exact (algebraMap F _).injective
  exact Algebra.TensorProduct.includeRight_injective hA

theorem ratM_det (γ : Matrix (Fin n) (Fin n) E) :
    (ratM F γ).det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ γ.det :=
  (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) γ).symm




theorem uEquiv_symm {a b : Matrix (Fin n) (Fin n) (RA F E)} (h : UEquiv c G L M a b) : UEquiv c G L M b a := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h
  have hd : IsUnit γ.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 := hγ.1
    rw [ratM_det, h0, TensorProduct.tmul_zero, isUnit_zero_iff] at h1
    exact zero_ne_one (α := E) (one_tmul_injective (F := F) (by simpa [Algebra.TensorProduct.one_def] using h1))
  have hi : ratM F γ⁻¹ * ratM F γ = 1 := by rw [← ratM_mul, nonsing_inv_mul γ hd, ratM_one]
  refine ⟨γ⁻¹, by rw [← inv_eq_left_inv hi]; exact isUA_inv c G hγ, k⁻¹, isKM_inv c G L M hk, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
    Matrix.one_mul]

end GlobalTheory.UCls.Model
