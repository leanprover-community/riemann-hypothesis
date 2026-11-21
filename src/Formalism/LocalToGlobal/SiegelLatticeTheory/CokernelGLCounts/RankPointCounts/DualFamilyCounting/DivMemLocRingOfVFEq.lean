import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem κι_eq (t : 𝓞 F) : κ (ι t) = algebraMap F K (t : F) := rfl

theorem κι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  intro h
  apply ha
  have h1 : ι a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [h1, map_zero])


variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

theorem mem_locRing_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (z : K) :
    z ∈ WA.locRing P ↔ ∃ t : 𝓞 F, t ∉ P.comap ι ∧ ∃ r : 𝓞 K, κ r = κ (ι t) * z := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [WA.mem_locRing, UnimodularLocalization.locR_eq_locF hK hF hP, LocF.mem_locF_iff hp]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Submodule.mem_one, Algebra.smul_def]



section Line

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_locF_span_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (x z : V) :
    z ∈ locF (P.comap ι) (Submodule.span (𝓞 K) {x}) ↔ ∃ c ∈ WA.locRing P, z = c • x := by
  have hp : (P.comap ι).IsPrime := Ideal.comap_isPrime _ _
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hz
    have ht0 : κ (ι t) ≠ 0 := κι_ne_zero (fun h => ht (h ▸ Ideal.zero_mem _))
    refine ⟨κ r / κ (ι t), (mem_locRing_iff hK hF hP _).2 ⟨t, ht, r, by field_simp⟩, ?_⟩
    have e1 : r • x = κ r • x := (algebraMap_smul K r x).symm
    have e2 : ι t • z = κ (ι t) • z := (algebraMap_smul K (ι t) z).symm
    rw [e1, e2] at hr
    rw [div_eq_inv_mul, mul_smul, hr, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, r, hr⟩ := (mem_locRing_iff hK hF hP c).1 hc
    refine ⟨t, ht, Submodule.mem_span_singleton.2 ⟨r, ?_⟩⟩
    rw [← algebraMap_smul K r x, ← algebraMap_smul K (ι t) (c • x), smul_smul, hr]

omit hK hF in
theorem h_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  ring



end Line

theorem exists_norm_congr_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ∉ 𝔭) {k : ℕ}
    (hk : 1 ≤ k) : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 k le_rfl hk (ι c) (idealPowerSpanBounds.conjO_map hF c) hcP
  by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have h3 := h1 hc'
    have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hpos : (0 : ℝ) < (normRepCount K (P ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos hs _) ?_
      have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hc']
    exact hα
  · have h3 := h2 hc'
    have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos (by linarith) _) ?_
      have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
        rw [Nat.cast_one, zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ hN
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.extP_split hK hF hP hc']
    exact hα

end Formalism.L2.SG.Pf.TemperedBoundGL3
