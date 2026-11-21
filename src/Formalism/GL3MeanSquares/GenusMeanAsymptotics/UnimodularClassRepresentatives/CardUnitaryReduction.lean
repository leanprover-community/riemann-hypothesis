import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSkewValue

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open HermitianSublattices idealPowerSpanBounds

namespace Cell

section Abs

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]

theorem map_skew (ρ : A →+* C) (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y))
    (hμm : ∀ a y, μ (ρ a * y) = a * μ y) (H : Matrix κ κ A) (Y : Matrix κ κ C) :
    (H.map ρ * Y + Yᴴ * H.map ρ).map μ = H * Y.map μ + (Y.map μ)ᴴ * H := by
  ext i l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, hμm,
    conjTranspose_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, hμm, hμs, mul_comm]

theorem quad_zero (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y)) (h2 : ∀ y z, μ y * μ z = 0)
    (H : Matrix κ κ A) (Y : Matrix κ κ C) : (Y.map μ)ᴴ * H * Y.map μ = 0 := by
  ext i l
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro m _
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hμs, mul_right_comm, h2, zero_mul]

theorem expand {H X0 : Matrix κ κ A} (hX0 : X0ᴴ * H * X0 = H) (D : Matrix κ κ A) :
    (X0 * (1 + D))ᴴ * H * (X0 * (1 + D)) = H + (H * D + Dᴴ * H) + Dᴴ * H * D := by
  rw [conjTranspose_mul, conjTranspose_add, conjTranspose_one]
  calc _ = (1 + Dᴴ) * (X0ᴴ * H * X0) * (1 + D) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hX0]; noncomm_ring


end Abs

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def muQ {𝔭 : Ideal (𝓞 F)} {j : ℕ} (c : ℕ) {d : 𝓞 F} (hd : d ∈ 𝔭 ^ j) :
    (𝓞 K ⧸ extP K 𝔭 ^ c) →+ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)) :=
  (Submodule.mapQ (extP K 𝔭 ^ c) (extP K 𝔭 ^ (j + c)) (LinearMap.mulLeft (𝓞 K) (ι d)) (by
    intro a ha
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, pow_add]
    exact Ideal.mul_mem_mul ((mem_pow_iff 𝔭 j d).2 hd) ha)).toAddMonoidHom


end Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

variable [Fact (IsFixF K F)]


end Formalism.HermitianLattices.Ext.L3.HU
