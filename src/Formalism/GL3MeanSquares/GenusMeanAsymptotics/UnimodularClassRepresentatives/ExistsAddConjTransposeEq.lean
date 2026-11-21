import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Mathlib

section
open Matrix TensorProduct

namespace Formalism.HermitianLattices.Ext.L3.LITr

section Det

variable {R : Type*} [CommRing R] {m : ℕ}

end Det

section Herm

variable {K F : Type*} [Field K] [CharZero K] [StarRing K] [Field F] [Algebra F K] {m : ℕ}

def hermSub (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) K) where
  carrier := {B | Bᴴ = B}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, show aᴴ = a from ha, show bᴴ = b from hb]
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c B hB
    change (c • B)ᴴ = c • B
    rw [← algebraMap_smul K c B, Matrix.conjTranspose_smul, show Bᴴ = B from hB, (hF _).2 ⟨c, rfl⟩]

variable (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))

theorem mem_hermSub (B : Matrix (Fin m) (Fin m) K) : B ∈ hermSub hF m ↔ Bᴴ = B := Iff.rfl

noncomputable def toMat (m : ℕ) : K ⊗[F] (hermSub hF m) →ₗ[K] Matrix (Fin m) (Fin m) K :=
  (hermSub hF m).subtype.liftBaseChange K

theorem toMat_tmul (a : K) (B : hermSub hF m) :
    toMat hF m (a ⊗ₜ B) = a • (B : Matrix (Fin m) (Fin m) K) := by
  simp [toMat]

include hF in
theorem exists_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (a : K) :
    ∃ x y : F, a = algebraMap F K x + δ * algebraMap F K y := by
  obtain ⟨x, hx⟩ := (hF ((a + star a) / 2)).1 (by
    rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
  obtain ⟨y, hy⟩ := (hF ((a - star a) / (2 * δ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hδ]
    field_simp
    ring)
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  field_simp
  ring

theorem exists_tensor_decomp {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (t : K ⊗[F] (hermSub hF m)) :
    ∃ B C : hermSub hF m, t = (1 : K) ⊗ₜ B + δ ⊗ₜ C := by
  induction t with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a B =>
    obtain ⟨x, y, rfl⟩ := exists_decomp hF hδ hδ0 a
    refine ⟨x • B, y • B, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_comm δ]
  | add s t hs ht =>
    obtain ⟨B, C, rfl⟩ := hs
    obtain ⟨B', C', rfl⟩ := ht
    refine ⟨B + B', C + C', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

theorem toMat_injective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Injective (toMat hF m) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨B, C, rfl⟩ := exists_tensor_decomp hF hδ hδ0 t
  rw [map_add, toMat_tmul, toMat_tmul, one_smul] at ht
  have ht' := congrArg Matrix.conjTranspose ht
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, (mem_hermSub hF _).1 B.2,
    (mem_hermSub hF _).1 C.2, hδ, Matrix.conjTranspose_zero, neg_smul] at ht'
  have hB : (B : Matrix (Fin m) (Fin m) K) = 0 := by
    have : (2 : K) • (B : Matrix (Fin m) (Fin m) K) = 0 := by
      rw [two_smul]
      calc _ = ((B : Matrix (Fin m) (Fin m) K) + δ • (C : Matrix (Fin m) (Fin m) K)) +
            ((B : Matrix (Fin m) (Fin m) K) + -(δ • (C : Matrix (Fin m) (Fin m) K))) := by abel
        _ = 0 := by rw [ht, ht', add_zero]
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have hC : (C : Matrix (Fin m) (Fin m) K) = 0 := by
    rw [hB, zero_add] at ht
    exact (smul_eq_zero.1 ht).resolve_left hδ0
  rw [Subtype.ext (a1 := B) (a2 := 0) hB, Subtype.ext (a1 := C) (a2 := 0) hC]
  simp

theorem toMat_surjective {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Surjective (toMat hF m) := by
  intro X
  have h1 : ((2 : K)⁻¹ • (X + Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_ofNat, add_comm]
  have h2 : ((2 * δ)⁻¹ • (X - Xᴴ)) ∈ hermSub hF m := by
    rw [mem_hermSub, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_inv₀, star_mul', star_ofNat, hδ, mul_neg, inv_neg,
      neg_smul, ← smul_neg, neg_sub]
  refine ⟨(1 : K) ⊗ₜ ⟨_, h1⟩ + δ ⊗ₜ ⟨_, h2⟩, ?_⟩
  rw [map_add, toMat_tmul, toMat_tmul, one_smul, smul_smul]
  have : δ * (2 * δ)⁻¹ = (2 : K)⁻¹ := by field_simp
  rw [this, ← smul_add]
  have : X + Xᴴ + (X - Xᴴ) = (2 : K) • X := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

noncomputable def toMatEquiv {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0) (m : ℕ) :
    K ⊗[F] (hermSub hF m) ≃ₗ[K] Matrix (Fin m) (Fin m) K :=
  LinearEquiv.ofBijective (toMat hF m) ⟨toMat_injective hF hδ hδ0, toMat_surjective hF hδ hδ0⟩

def conjHerm (P : Matrix (Fin m) (Fin m) K) : hermSub hF m →ₗ[F] hermSub hF m where
  toFun B := ⟨Pᴴ * (B : Matrix (Fin m) (Fin m) K) * P, by
    rw [mem_hermSub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, (mem_hermSub hF _).1 B.2, Matrix.mul_assoc]⟩
  map_add' B C := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c B := by
    apply Subtype.ext
    simp

end Herm

end Formalism.HermitianLattices.Ext.L3.LITr
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  have htop : LinearMap.range (idealPowerSpanBounds.trF hF) = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (idealPowerSpanBounds.trF hF)) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← idealPowerSpanBounds.trF_spec hF]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have h1 : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [pow_one])
    have h0 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range (idealPowerSpanBounds.trF hF) := htop ▸ Submodule.mem_top
  exact ⟨z, by rw [← idealPowerSpanBounds.trF_spec hF, hz]⟩

end Formalism.HermitianLattices.Ext.L3
end
end
