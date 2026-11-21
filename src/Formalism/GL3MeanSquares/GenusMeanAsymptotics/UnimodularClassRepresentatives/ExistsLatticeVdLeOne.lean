import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CongrPIffInI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

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
      simp only [map_add, LinearMap.add_apply, ← hdd]
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

theorem exists_F_smul_mem (hF : IsFixF K F) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ)
    (v : V) : ∃ s : 𝓞 F, s ≠ 0 ∧ ι s • v ∈ Λ := by
  obtain ⟨r, hr, hrv⟩ := StabilizerLattices.exists_smul_mem hΛ v
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K r * r)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · apply hr
      rw [← conjO_conjO r, h0, map_zero]
    · exact hr h0
  · rw [hs, mul_smul]
    exact Λ.smul_mem _ hrv

theorem exists_near (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hL : Submodule.IsLattice K A) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = κ (ι n)) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ := hrep
  obtain ⟨s, hs0, hsb⟩ := exists_F_smul_mem hF hL b
  have hN : 4 * (s * s * n) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)
  refine ⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩
  set v := vF 𝔭 (4 * (s * s * n)) with hv
  by_cases h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))
  · by_cases h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))
    · exfalso
      apply localValuationFiltration.notMem_pow_vF h𝔭 hN
      rw [← hv, ← inI_ι (K := K) h𝔭]
      have h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n))) := by
        have := InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))
        rwa [zero_add] at this
      have e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) +
          κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n)) := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]
        ring
      rw [e]
      exact (h1.add hp h2).sub hp h3
    · exact exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb)
        (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2
  · exact exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1

end Formalism.HermitianLattices.Ext.L3.Cell
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem exists_of_normRepCount_ne_zero {Q : Ideal (𝓞 K)} {n : 𝓞 K} (h : normRepCount K Q 1 n ≠ 0) :
    ∃ α : 𝓞 K, conjO K α * α - n ∈ Q := by
  unfold normRepCount at h
  obtain ⟨⟨x, y, -, hy⟩⟩ := (Nat.card_ne_zero.mp h).1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hy
  exact Ideal.Quotient.eq.mp hy

theorem exists_norm_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ∉ 𝔭) : ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ ν - c ∈ 𝔭 := by
  obtain ⟨P, hP, hPp⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (hPp ▸ Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  have key : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ P := by
    obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 1 le_rfl le_rfl (ι c) (conjO_map hF c) hcP
    by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
    · have h3 := h1 hc'
      have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
      have hpos : (0 : ℝ) < (normRepCount K (P ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos hs _) ?_
        have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      exact ⟨α, by simpa using hα⟩
    · have h3 := h2 hc'
      have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) 1 (ι c) : ℝ) := by
        rw [h3]
        refine mul_pos (pow_pos (by linarith) _) ?_
        have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
          rw [Nat.cast_one, zpow_neg_one]
          exact inv_lt_one_of_one_lt₀ hN
        linarith
      obtain ⟨α, hα⟩ := exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
      rw [pow_one] at hα
      exact ⟨α, Ideal.mul_le_left hα⟩
  obtain ⟨α, hα⟩ := key
  obtain ⟨ν, hν⟩ := (conjO_eq_iff_mem_range hF (conjO K α * α)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨α, ν, hν.symm, ?_⟩
  rw [← hPp, Ideal.mem_comap, map_sub, hν]
  exact hα

theorem exists_scale (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} {r k : ℕ}
    (h1 : a₁ ∈ 𝔭 ^ (r + r + k)) (h2 : a₁ ∉ 𝔭 ^ (r + r + k + 1)) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ (k + 1) := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  obtain ⟨g, hg, hg'⟩ := Ideal.exists_mem_pow_notMem_pow_succ 𝔭 hp0 h𝔭.ne_top r
  have hgg : g * g ∉ 𝔭 ^ (r + r + 1) := mul_notMem hp hp0 hg' hg'
  have hgg0 : g * g ≠ 0 := fun h0 => hgg (h0 ▸ zero_mem _)
  have hg0 : g ≠ 0 := fun h0 => hgg0 (by rw [h0, zero_mul])
  have hκg := κι_ne_zero (K := K) hg0
  have hκgg := κι_ne_zero (K := K) hgg0
  set d := (κ (ι (g * g)))⁻¹ * κ (ι a₁) with hd
  have hd1 : InI 𝔭 k d := InI.div h𝔭 hgg0 hgg ((inI_ι h𝔭).2 h1)
  have hd2 : ¬ InI 𝔭 (k + 1) d := by
    intro hcon
    apply h2
    rw [← inI_ι (K := K) h𝔭]
    have e : κ (ι a₁) = κ (ι (g * g)) * d := by rw [hd]; field_simp
    rw [e, add_assoc]
    refine InI.mul hp ((inI_ι h𝔭).2 ?_) hcon
    rw [pow_add]
    exact Ideal.mul_mem_mul hg hg
  have hds : star d = d := by rw [hd, star_mul', star_inv₀, star_ι hF, star_ι hF]
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hds (hd1.mono (Nat.zero_le _))
  have hκt := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  refine ⟨κ (ι t) * (κ (ι g))⁻¹, mul_ne_zero hκt (inv_ne_zero hκg), ?_, t * δ, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_ι hF, star_ι hF]
  · rw [map_mul ι, map_mul κ, e, hd, map_mul ι g g, map_mul κ]
    field_simp
  · intro hcon
    apply hd2
    apply InI.of_mul hp ht
    apply InI.of_mul hp ht
    rw [← e, ← map_mul, ← map_mul]
    exact (inI_ι h𝔭).2 hcon

theorem exists_scale_int (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a₁ : 𝓞 F} (h0 : a₁ ≠ 0) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * κ (ι a₁) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have h1 := localValuationFiltration.mem_pow_vF h𝔭 h0
  have h2 := localValuationFiltration.notMem_pow_vF h𝔭 h0
  have e : vF 𝔭 a₁ = vF 𝔭 a₁ / 2 + vF 𝔭 a₁ / 2 + vF 𝔭 a₁ % 2 := by omega
  rw [e] at h1 h2
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale (K := K) hF h𝔭 h1 h2
  exact ⟨μ, hμ0, hμs, a, ha, fun hm => ha' (Ideal.pow_le_pow_right (by omega) hm)⟩

theorem exists_scale_fixed (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {d : K} (hd0 : d ≠ 0)
    (hds : star d = d) :
    ∃ μ : K, μ ≠ 0 ∧ star μ = μ ∧ ∃ a : 𝓞 F, μ * μ * d = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  obtain ⟨f, rfl⟩ := (hF d).1 hds
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hκy := κι_ne_zero (K := K) hy0
  have e : algebraMap F K (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) = κ (ι x) / κ (ι y) := by
    rw [map_div₀]; rfl
  rw [e] at hd0 ⊢
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hd0
    simp
  obtain ⟨μ, hμ0, hμs, a, ha, ha'⟩ := exists_scale_int (K := K) hF h𝔭 (mul_ne_zero hy0 hx0)
  refine ⟨μ * κ (ι y), mul_ne_zero hμ0 hκy, by rw [star_mul', hμs, star_ι hF], a, ?_, ha'⟩
  rw [← ha, map_mul ι, map_mul κ]
  field_simp

theorem exists_alpha (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ∈ 𝔭) (ha2 : a ∉ 𝔭 ^ 2) (ha' : a' ∈ 𝔭) (ha'2 : a' ∉ 𝔭 ^ 2) :
    ∃ α : 𝓞 K, ∃ ν : 𝓞 F, conjO K α * α = ι ν ∧ a * ν + a' ∈ 𝔭 ^ 2 ∧ a * ν + a' ∉ 𝔭 ^ 3 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have h1 : -a' ∈ Ideal.span {a} ⊔ 𝔭 ^ 2 :=
    pow_le_span_sup hp hp0 (c := 1) (by simpa using ha2) 2 (by simpa using ha')
  obtain ⟨c, r, hr, e⟩ := Ideal.mem_span_singleton_sup.1 h1
  have hc : c ∉ 𝔭 := by
    intro hc
    apply ha'2
    have : a' = -(c * a + r) := by rw [e]; ring
    rw [this]
    refine neg_mem (add_mem ?_ hr)
    rw [pow_two]
    exact Ideal.mul_mem_mul hc ha
  obtain ⟨α₀, ν₀, hν₀, hνc⟩ := exists_norm_congr hK hF h𝔭 hc
  have hν₀p : ν₀ ∉ 𝔭 := fun h => hc (by simpa using sub_mem h hνc)
  have h2 : a * ν₀ + a' ∈ 𝔭 ^ 2 := by
    have : a * ν₀ + a' = a * (ν₀ - c) - r := by linear_combination e
    rw [this]
    refine sub_mem ?_ hr
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hνc
  by_cases h3 : a * ν₀ + a' ∈ 𝔭 ^ 3
  · obtain ⟨τ, hτ⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    obtain ⟨t₂, ht₂⟩ := (conjO_eq_iff_mem_range hF (conjO K τ * τ)).1 (by
      rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨α₀ * (1 + ι a * τ), ν₀ * (1 + a + a * a * t₂), ?_, ?_, ?_⟩
    · rw [map_mul, map_add, map_mul, map_one, conjO_map hF, map_mul ι, map_add ι, map_add ι, map_mul ι,
        map_mul ι, map_one, ← hν₀, ht₂]
      rw [map_one] at hτ
      linear_combination (conjO K α₀ * α₀ * ι a) * hτ
    · have : a * (ν₀ * (1 + a + a * a * t₂)) + a' =
          (a * ν₀ + a') + a * a * (ν₀ * (1 + a * t₂)) := by ring
      rw [this]
      refine add_mem h2 (Ideal.mul_mem_right _ _ ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul ha ha
    · intro hcon
      have h4 : a * a * a * (ν₀ * t₂) ∈ 𝔭 ^ 3 := by
        refine Ideal.mul_mem_right _ _ ?_
        rw [pow_succ, pow_two]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul ha ha) ha
      have ha2' : a ∉ 𝔭 ^ (1 + 1) := by simpa using ha2
      have hν' : ν₀ ∉ 𝔭 ^ (0 + 1) := by simpa using hν₀p
      have h5 : a * a * ν₀ ∉ 𝔭 ^ 3 := by
        have := mul_notMem hp hp0 (mul_notMem hp hp0 ha2' ha2') hν'
        simpa using this
      apply h5
      have : a * a * ν₀ = (a * (ν₀ * (1 + a + a * a * t₂)) + a') - (a * ν₀ + a') -
          a * a * a * (ν₀ * t₂) := by ring
      rw [this]
      exact sub_mem (sub_mem hcon h3) h4
  · exact ⟨α₀, ν₀, hν₀, h2, h3⟩

end Formalism.HermitianLattices.Ext.L3.Cell
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem symm0 {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e : starRingEnd K (h x y) = h y x := by
    first
    | exact hs.eq x y
    | exact hs x y
  rw [hxy, map_zero] at e
  exact e.symm

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
    ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
  have hds : star (h e e) = h e e := by
    have e' : starRingEnd K (h e e) = h e e := by
      first
      | exact hs.eq e e
      | exact hs e e
    rwa [starRingEnd_apply] at e'
  obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
  exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩

theorem exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
    (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
    (hap : a ∈ 𝔭) :
    ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
      h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
  have hez := symm0 hs hze
  obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
  have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
  set W := c * ν + a with hW
  have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
  have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
  have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
  obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
    (by simpa using hW2) (by simpa using hW3)
  obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
    (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
  have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
  refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
    ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
  · rw [form_smul_smul, hμ₁s, ← hb₁]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
    linear_combination κ (ι c) * hν'
  · rw [form_smul_smul, hμ₂s, ← hb₂]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
    linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
  · rw [form_smul_smul]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
    ring
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]

theorem κι_inj {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by
  have e : ∀ c : 𝓞 F, κ (ι c) = algebraMap F K (c : F) := fun c => rfl
  rw [e, e] at hab
  exact RingOfIntegers.ext ((algebraMap F K).injective hab)

variable [FiniteDimensional K V]

theorem exists_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {x₀ : V} {n : 𝓞 F}
    (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
      (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
      (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
      (z = x₀ ∨ ∃ i, y i = x₀) := by
  have hp := h𝔭.isPrime
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  | succ r ih =>
    intro hr
    obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
    obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
      (by omega)
    obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
    have hze : h z (μ • e₀) = 0 := by
      have := hoe 0
      rw [Fin.cons_zero] at this
      rw [map_smul, this, smul_zero]
    have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
      have := hoe i.succ
      rw [Fin.cons_succ] at this
      rw [map_smul, this, smul_zero]
    set e := μ • e₀ with he
    have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
        b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
        (u = x₀ ∨ ∃ i, y i = x₀) := by
      by_cases hcp : c ∈ 𝔭
      · have hx₀' : ∃ i, y i = x₀ := by
          rcases hx₀ with rfl | h1
          · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
          · exact h1
        by_cases hap : ae ∈ 𝔭
        · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
            exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
          exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
            fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
        · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
            fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
      · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
          fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
    obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
    refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
      · intro hij
        rw [Fin.cons_succ, Fin.cons_succ]
        exact ho i j fun hh => hij (by rw [hh])
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact h5
      · rw [Fin.cons_succ]; exact (h6 i).2
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
      · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
    · rcases h7 with rfl | ⟨i, hi⟩
      · exact ⟨0, by rw [Fin.cons_zero]⟩
      · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩

end Formalism.HermitianLattices.Ext.L3.Cell
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem isLattice_spanO {N : ℕ} (e : Basis (Fin N) K V) : Submodule.IsLattice K (spanO e) where
  fg := Submodule.fg_span (Set.finite_range e)
  span_eq_top := by
    rw [eq_top_iff, ← e.span_eq]
    exact Submodule.span_mono Submodule.subset_span

theorem integral_spanO {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i))) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (spanO e) := by
  intro x hx y hy
  have hH : ∀ i j, κ ((Matrix.diagonal fun i => ι (A' i)) i j) = h (e i) (e j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, ho i j hij]
  have := form_eq h e hH ⟨x, hx⟩ ⟨y, hy⟩
  exact Submodule.mem_one.2 ⟨_, this.symm⟩

theorem vd_le_one_of_basis {h : V →ₗ⋆[K] V →ₗ[K] K} {N : ℕ} (hN : finrank K V = N)
    (e : Basis (Fin N) K V) (A' : Fin N → 𝓞 F)
    (ho : ∀ i j, i ≠ j → h (e i) (e j) = 0) (hn : ∀ i, h (e i) (e i) = κ (ι (A' i)))
    (hprod : ∏ i, A' i ∉ 𝔭 ^ 2) : vd h (spanO e) 𝔭 ≤ 1 := by
  subst hN
  unfold vd
  refine csSup_le' fun E hE => ?_
  by_contra hlt
  apply hprod
  rw [← mem_pow_iff (K := K)]
  apply Ideal.pow_le_pow_right (by omega : 2 ≤ E)
  apply hE
  refine Ideal.subset_span ⟨e, fun i => Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  have : (Matrix.of fun i j => h (e i) (e j)) = Matrix.diagonal fun i => κ (ι (A' i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.of_apply, hn]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.of_apply, ho i j hij]
  rw [this, Matrix.det_diagonal, map_prod, map_prod]

variable [FiniteDimensional K V]

theorem exists_lattice (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have han := LocF.aniso_of_totPosDef hd
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact κι_ne_zero (K := K) (ne_zero_of_notMem hn) hx.symm
  have hm : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩
  obtain ⟨r, hr⟩ : ∃ r, finrank K V = r + 1 := ⟨finrank K V - 1, by omega⟩
  obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ :=
    exists_family hK hF h𝔭 hs han hx hn r (by omega)
  have hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact absurd rfl hij
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact hzy j
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (hzy i)
    · intro hij
      rw [Fin.cons_succ, Fin.cons_succ]
      exact ho i j fun hh => hij (by rw [hh])
  have hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) =
      κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, Fin.cons_zero]; exact hnz
    · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
  have hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2 := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hc2' : c ∉ 𝔭 ^ (1 + 1) := by simpa using hc2
    have hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1) := by simpa using hprod
    have := mul_notMem hp hp0 hc2' hprod'
    simpa using this
  have hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0 := by
    intro i
    rw [hnf]
    refine κι_ne_zero fun h0 => hP ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    exact zero_mem _
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne
  refine ⟨spanO e, isLattice_spanO e,
    integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i), ?_,
    vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i) hP⟩
  rcases hx₀ with rfl | ⟨i, hi⟩
  · exact Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩
  · exact Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩

end Formalism.HermitianLattices.Ext.L3.Cell
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem algebraMap_int_F_to_K_eq_algebraMap_F_K (n : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := by
  rw [← IsScalarTower.algebraMap_apply]
  first
  | exact IsScalarTower.algebraMap_apply (𝓞 F) F K n
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl)
  | simp

theorem exists_exact_near (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = algebraMap F K (n : F)) :
    ∃ c₀ : ℕ, ∀ k : ℕ, c₀ ≤ k → ∀ x ∈ (locF 𝔭 A₀), CongrP 𝔭 k (h x x) (algebraMap F K (n : F)) →
      ∃ y ∈ (locF 𝔭 A₀), h y y = algebraMap F K (n : F) ∧
        y - x ∈ ((extP K 𝔭) ^ (k - c₀) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨v, hv⟩ := Cell.exists_near (𝔭 := 𝔭) h𝔭 hF hs hA₀ hA₀i hn
    (by obtain ⟨b, hb⟩ := hrep; exact ⟨b, by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hb⟩)
  refine ⟨v + 1, fun k hk x hx hc => ?_⟩
  rw [Cell.congrP_iff_inI] at hc
  obtain ⟨y, hy0, hyy, hyx⟩ := hv (k - v) (by omega) x ((WCA.inL_zero_iff hp).2 hx)
    (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K, show v + (k - v) = k by omega]; exact hc)
  refine ⟨y, (WCA.inL_zero_iff hp).1 hy0, by rw [hyy, algebraMap_int_F_to_K_eq_algebraMap_F_K], ?_⟩
  exact (WCA.InL.mono (by omega) hyx).mem hp

theorem exists_lattice_vd_le_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap F K (n : F)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  exact Cell.exists_lattice (𝔭 := 𝔭) hK hF hs hd h𝔭 (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hx) hn

end Formalism.HermitianLattices.Ext.L3
end
end
