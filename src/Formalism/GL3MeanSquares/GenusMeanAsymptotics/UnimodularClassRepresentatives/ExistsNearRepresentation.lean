module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem form_self_star {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (w : V) : star (h w w) = h w w :=
  hs.eq w w

theorem exact_step {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {b x : V}
    (hd : h (x - b) (x - b) ≠ 0) :
    h (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b))
        (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) = h b b ∧
      (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) - x =
        -(((h (x - b) (x - b))⁻¹ * (h x x - h b b)) • (x - b)) := by
  set w := x - b with hw
  have hx : x = w + b := by rw [hw]; abel
  have e1 : star (h b w) = h w b := hs.eq b w
  have e2 : star (h w b) = h b w := hs.eq w b
  have e3 : star (h w w) = h w w := hs.eq w w
  set d := h w w with hdd
  constructor
  · simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, star_mul', star_add, star_inv₀, e1, e2, e3, ← hdd]
    field_simp
    ring
  · have e4 : h x x - h b b = d + (h b w + h w b) := by
      rw [hx]
      simp only [map_add (f := _), LinearMap.add_apply, ← hdd]
      ring
    rw [e4]
    have e5 : d⁻¹ * (d + (h b w + h w b)) = 1 + (h b w + h w b) * d⁻¹ := by
      field_simp
    rw [e5, add_smul, one_smul]
    conv_lhs => rw [hx]
    abel

theorem exists_near_representation (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n s : 𝓞 F} {b : V}
    (hb : h b b = κ (ι n)) (hsb : ι s • b ∈ A) {v k : ℕ} {x : V} (hx : InL 𝔭 A 0 x)
    (hε : InI 𝔭 (v + k) (h x x - κ (ι n)))
    (hD : ¬ InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))) :
    ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hd : h (x - b) (x - b) ≠ 0 := by
    intro h0
    apply hD
    rw [h0, mul_zero]
    exact InI.zero hp _
  have hs0 : κ (ι s) ≠ 0 := by
    intro h0
    apply hD
    rw [map_mul, map_mul, h0, zero_mul, zero_mul]
    exact InI.zero hp _
  obtain ⟨h1, h2⟩ := exact_step hs hd
  set y := b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b) with hy
  set w := x - b with hw
  have hsw : InL 𝔭 A 0 (ι s • w) := by
    rw [hw, smul_sub]
    refine InL.sub hp ?_ ((inL_zero_iff hp).2 (le_locF 𝔭 A hsb))
    rw [← algebraMap_smul K (ι s)]
    have := InL.smul hp (InI.int hp (ι s)) hx
    rwa [zero_add] at this
  have hDe : h (ι s • w) (ι s • w) = κ (ι (s * s)) * h w w := form_smul hF h s s w w
  have hD0 : InI 𝔭 0 (κ (ι (s * s)) * h w w) := by
    rw [← hDe]
    exact InL.form hp hF hA hsw hsw
  have hDs : star (κ (ι (s * s)) * h w w) = κ (ι (s * s)) * h w w := by
    rw [← hDe]; exact hs.eq _ _
  have h3 : InI 𝔭 (v + k) (κ (ι s) * (h x x - κ (ι n))) := by
    have := InI.mul hp (InI.int hp (ι s)) hε
    rwa [zero_add] at this
  have h4 := InI.divK h𝔭 hF hDs hD0 hD h3
  have h5 := InL.smul hp h4 hsw
  rw [add_zero] at h5
  have h6 : InL 𝔭 A k (y - x) := by
    rw [h2, hb]
    apply InL.neg
    have : ((h w w)⁻¹ * (h x x - κ (ι n))) • w =
        ((κ (ι (s * s)) * h w w)⁻¹ * (κ (ι s) * (h x x - κ (ι n)))) • ι s • w := by
      rw [← algebraMap_smul K (ι s), smul_smul]
      congr 1
      rw [map_mul, map_mul]
      field_simp
    rw [this]
    exact h5
  refine ⟨y, ?_, h1.trans hb, h6⟩
  have : y = x + (y - x) := by abel
  rw [this]
  exact hx.add hp (h6.mono (Nat.zero_le _))

end Formalism.HermitianLattices.Ext.L3.Cell
