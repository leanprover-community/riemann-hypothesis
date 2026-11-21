import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMemLocRingOfVFEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsAlt

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds : JordSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem exists_F_mul_int (hF : IsFixF K F) (z : K) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ ∃ r : 𝓞 K, κ (ι s) * z = κ r := by
  obtain ⟨a, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) z
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  have hκm : κ m ≠ 0 := fun h0 =>
    hm0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K m * m)).1
    (by rw [map_mul, WA.conjO_conjO, mul_comm])
  refine ⟨s, ?_, conjO K m * a, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · exact hm0 (by rw [← WA.conjO_conjO m, h0, map_zero])
    · exact hm0 h0
  · rw [hs, map_mul, map_mul]
    field_simp

section Near

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem exists_near_of_smul (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0) {b : V}
    (hb : h b b = κ (ι n)) {s : 𝓞 F} (hs0 : s ≠ 0) (hsb : ι s • b ∈ A) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
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

theorem isIntegral_span {J : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (c : J → V)
    (hc : ∀ i j, h (c i) (c j) ∈ (1 : Submodule (𝓞 K) K)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (Submodule.span (𝓞 K) (Set.range c)) := by
  have hsm : ∀ (r : 𝓞 K) (v : V), r • v = κ r • v := fun r v => (algebraMap_smul K r v).symm
  have key : ∀ i, ∀ y ∈ Submodule.span (𝓞 K) (Set.range c),
      h (c i) y ∈ (1 : Submodule (𝓞 K) K) := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hc i j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hy
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact key i y hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx =>
    rw [hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← WA.algebraMap_conjO, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

end Near

section Exact

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem notMem_zero {𝔭 : Ideal (𝓞 F)} {d : 𝓞 F} (hd : d ∉ 𝔭) : d ≠ 0 :=
  fun h0 => hd (h0 ▸ Ideal.zero_mem _)

theorem exactAt_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {π : K} (hπ : IsUnif (locRing P) π) :
    G3.ExactAt (locRing P) π h := by
  intro J _ _ b e i₀ ho hu hmin ξ hξ hξu
  have hPp := hP.isPrime
  set 𝔭 := P.comap ι with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have hπS : ∀ m : ℕ, π ^ m ∈ locRing P := fun m => (locRing P).pow_mem hπ.mem m
  have hnormS : ∀ (v : V) (m : ℕ), IsUnitIn (locRing P) (h v v * (π ^ m)⁻¹) →
      h v v ∈ locRing P ∧ h v v ≠ 0 := by
    intro v m hv
    have hπm : π ^ m ≠ 0 := pow_ne_zero _ hπ.ne
    refine ⟨?_, ?_⟩
    · have e1 : h v v = h v v * (π ^ m)⁻¹ * π ^ m := by field_simp
      rw [e1]
      exact (locRing P).mul_mem hv.2.1 (hπS m)
    · intro h0
      apply hv.1
      rw [h0, zero_mul]
  have hfix : ∀ v : V, star (h v v) = h v v := fun v => hs.eq v v
  have hfrac : ∀ (v : V) (m : ℕ), IsUnitIn (locRing P) (h v v * (π ^ m)⁻¹) →
      ∃ f d : 𝓞 F, d ∉ 𝔭 ∧ h v v = κ (ι f) / κ (ι d) := by
    intro v m hv
    obtain ⟨t, s, hs', he⟩ := U0.exists_frac_of_fixed hF hPp (hnormS v m hv).1 (hfix v)
    exact ⟨t, s, hs', he⟩
  choose f d hd hfd using fun i => hfrac (b i) (e i) (hu i)
  obtain ⟨n₁, d₀, hd₀, hξn⟩ := hfrac ξ (e i₀) hξu
  have hB0 := (hnormS _ _ (hu i₀)).2
  have hr : IsUnitIn (locRing P) (h ξ ξ / h (b i₀) (b i₀)) := by
    have hπm : π ^ e i₀ ≠ 0 := pow_ne_zero _ hπ.ne
    have e1 : h ξ ξ / h (b i₀) (b i₀) =
        (h ξ ξ * (π ^ e i₀)⁻¹) * (h (b i₀) (b i₀) * (π ^ e i₀)⁻¹)⁻¹ := by
      field_simp
    rw [e1]
    exact unit_mul hξu (unit_inv (hu i₀))
  obtain ⟨c, s, hs₀, hcs⟩ := U0.exists_frac_of_fixed hF hPp hr.2.1
    (by rw [star_div₀, hfix, hfix])
  have hc₀ : c ∉ 𝔭 := by
    intro hc
    have hu' := hr
    rw [hcs] at hu'
    have h1 := (WA.isUnitIn_div_iff hPp (ι c) (U0.mem_hcompl_of_notMem hF hPp hs₀)).1 hu'
    exact ((WA.mem_hcompl_iff hPp _).1 h1).1 hc
  have hcs𝔭 : c * s ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hc₀ hs₀
  have hD0 : κ (ι d₀) ≠ 0 := κι_ne_zero (notMem_zero hd₀)
  have hS0 : κ (ι s) ≠ 0 := κι_ne_zero (notMem_zero hs₀)
  have hE0 : κ (ι (d i₀)) ≠ 0 := κι_ne_zero (notMem_zero (hd i₀))

  let bb : J → V := fun i => κ (ι (d i)) • b i
  let A : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range bb)
  have hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A := by
    refine isIntegral_span bb fun i j => ?_
    by_cases hij : i = j
    · subst hij
      refine Submodule.mem_one.2 ⟨ι (d i * f i), ?_⟩
      show κ (ι (d i * f i)) = h (κ (ι (d i)) • b i) (κ (ι (d i)) • b i)
      have hdi : κ (ι (d i)) ≠ 0 := κι_ne_zero (notMem_zero (hd i))
      rw [h_smul_smul, hfd i, localizedQuotients.star_ι hF]
      simp only [map_mul]
      field_simp
    · show h (κ (ι (d i)) • b i) (κ (ι (d j)) • b j) ∈ _
      rw [h_smul_smul, ho i j hij, mul_zero]
      exact Submodule.zero_mem _
  have hmemS : ∀ y, InL 𝔭 A 0 y → y ∈ G3.spanS (locRing P) b := by
    rintro y ⟨t, ht, hty⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hty
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    have ht0 : κ (ι t) ≠ 0 := κι_ne_zero (notMem_zero ht)
    refine ⟨fun i => κ (g i * ι (d i)) / κ (ι t),
      fun i => U0.div_mem_locRing hPp _ (U0.mem_hcompl_of_notMem hF hPp ht), ?_⟩
    have e1 : y = (κ (ι t))⁻¹ • (ι t • y) := by
      rw [← algebraMap_smul K (ι t) y, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e1, ← hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bb]
    rw [← algebraMap_smul K (g i), smul_smul, smul_smul, map_mul]
    congr 1
    ring

  obtain ⟨β, hβ⟩ : ∃ β : V, β = κ (ι d₀) • ξ := ⟨_, rfl⟩
  have hn₁ : n₁ ≠ 0 := by
    rintro rfl
    apply (hnormS ξ _ hξu).2
    rw [hξn]
    simp
  have hβn : h β β = κ (ι (d₀ * n₁)) := by
    rw [hβ, h_smul_smul, hξn, localizedQuotients.star_ι hF]
    simp only [map_mul]
    field_simp
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hξ
  choose sj hsj0 rj hrj using fun j => exists_F_mul_int (K := K) hF (κ (ι d₀) * γ j / κ (ι (d j)))
  have hs'0 : (∏ j, sj j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hsj0 j
  have hs'β : ι (∏ j, sj j) • β ∈ A := by
    have e : ι (∏ j, sj j) • β = ∑ j, (ι (∏ k ∈ Finset.univ.erase j, sj k) * rj j) • bb j := by
      rw [← algebraMap_smul K (ι (∏ j, sj j)) β, hβ, ← hγ, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul K (ι (∏ k ∈ Finset.univ.erase j, sj k) * rj j) (bb j)]
      simp only [bb, smul_smul]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ sj (Finset.mem_univ j)]
      have hdj : κ (ι (d j)) ≠ 0 := κι_ne_zero (notMem_zero (hd j))
      have h1 := hrj j
      simp only [map_mul] at h1 ⊢
      rw [← h1]
      field_simp
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨v, hv⟩ := exists_near_of_smul h𝔭 hF hs hA
    (mul_ne_zero (notMem_zero hd₀) hn₁) hβn hs'0 hs'β

  obtain ⟨α, hα⟩ := exists_norm_congr_pow hK hF h𝔭 hcs𝔭 (show 1 ≤ v + 1 by omega)
  obtain ⟨x, hx⟩ : ∃ x : V, x = (κ (ι d₀) * κ α / κ (ι s)) • b i₀ := ⟨_, rfl⟩
  have hxL : InL 𝔭 A 0 x := by
    refine ⟨s * d i₀, fun hm => (hp.mem_or_mem hm).elim hs₀ (hd i₀), ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    have e : ι (s * d i₀) • x = (ι d₀ * α) • bb i₀ := by
      rw [← algebraMap_smul K (ι (s * d i₀)) x, ← algebraMap_smul K (ι d₀ * α) (bb i₀), hx]
      simp only [bb, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i₀, rfl⟩)
  have hF0 : κ (ι (f i₀)) = h (b i₀) (b i₀) * κ (ι (d i₀)) := by
    rw [hfd i₀]
    field_simp
  have hN1 : κ (ι n₁) = κ (ι d₀) * (κ (ι c) / κ (ι s) * h (b i₀) (b i₀)) := by
    have e2 : h ξ ξ = κ (ι c) / κ (ι s) * h (b i₀) (b i₀) := by
      have e3 := hcs
      unfold toK at e3
      rw [← e3]
      field_simp
    rw [← e2, hξn]
    field_simp
  have hε : InI 𝔭 (v + 1) (h x x - κ (ι (d₀ * n₁))) := by
    refine ⟨s * s * d i₀, fun hm => (hp.mem_or_mem hm).elim
        (fun hm' => (hp.mem_or_mem hm').elim hs₀ hs₀) (hd i₀),
      ι (d₀ * d₀ * f i₀) * (conjO K α * α - ι (c * s)), Ideal.mul_mem_left _ _ hα, ?_⟩
    rw [hx, h_smul_smul]
    simp only [map_mul, map_sub, WA.algebraMap_conjO, star_mul', star_div₀, localizedQuotients.star_ι hF, hF0, hN1]
    field_simp
  obtain ⟨y, hyL, hyy, -⟩ := hv 1 le_rfl x hxL hε
  obtain ⟨g, hg, rfl⟩ := hmemS y hyL
  have hinv : (κ (ι d₀))⁻¹ ∈ locRing P := by
    have := U0.div_mem_locRing hPp 1 (U0.mem_hcompl_of_notMem hF hPp hd₀)
    rwa [map_one, one_div] at this
  refine ⟨(κ (ι d₀))⁻¹ • ∑ i, g i • b i, ⟨fun i => (κ (ι d₀))⁻¹ * g i,
    fun i => (locRing P).mul_mem hinv (hg i), by rw [Finset.smul_sum]; simp only [smul_smul]⟩, ?_⟩
  rw [h_smul_smul, hyy, hξn, star_inv₀, localizedQuotients.star_ι hF]
  simp only [map_mul]
  field_simp

end Exact

theorem exact_vector_holds : G3.ExactVec := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs _ P hP π hπ
  exact exactAt_locRing hK hF hs hP hπ

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

private theorem vF_spec_of_ne_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    a ∈ 𝔭 ^ vF 𝔭 a ∧ a ∉ 𝔭 ^ (vF 𝔭 a + 1) := by
  have hbot : ∃ N, a ∉ 𝔭 ^ N := by
    by_contra hcon
    push_neg at hcon
    have hinf : a ∈ ⨅ i, 𝔭 ^ i := Submodule.mem_iInf _ |>.mpr hcon
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot] at hinf
    exact ha hinf
  obtain ⟨N, hN⟩ := hbot
  have hbdd : BddAbove {e : ℕ | a ∈ 𝔭 ^ e} := ⟨N, fun e he => by
    by_contra hlt
    push_neg at hlt
    exact hN (Ideal.pow_le_pow_right hlt.le he)⟩
  have hmem : a ∈ 𝔭 ^ vF 𝔭 a := Nat.sSup_mem ⟨0, by simp⟩ hbdd
  refine ⟨hmem, fun h => ?_⟩
  have hle : vF 𝔭 a + 1 ≤ vF 𝔭 a := le_csSup hbdd h
  omega

private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha

theorem exists_mul_eq_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ 𝔭 ^ vF 𝔭 a) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c : 𝓞 F, t * a' = c * a := by
  obtain ⟨hmem, hnot⟩ := vF_spec_of_ne_zero h𝔭 ha
  obtain ⟨J, hJ⟩ : 𝔭 ^ vF 𝔭 a ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hJp : ¬ J ≤ 𝔭 := fun hle => hnot (by
    have hs : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp hs)
  obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
  have hat : a' * t ∈ Ideal.span {a} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ha' htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hat
  exact ⟨t, htp, c, by rw [mul_comm, hc]⟩

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

theorem div_mem_locRing_of_mem_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a a' : 𝓞 F}
    (ha : a ≠ 0) (ha' : a' ∈ (P.comap ι) ^ vF (P.comap ι) a) :
    κ (ι a') / κ (ι a) ∈ locRing P := by
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  obtain ⟨t, ht, c, hc⟩ := exists_mul_eq_of_mem_pow hPm ha ha'
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  have e : κ (ι t) * (κ (ι a') / κ (ι a)) = κ (ι c) := by
    rw [← mul_div_assoc, ← map_mul, ← map_mul, hc, map_mul, map_mul, mul_div_cancel_right₀ _ hκa]
  show κ (ι a') / κ (ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  have hfix : star (κ (ι t)) = κ (ι t) := (hF _).mpr ⟨(t : F), by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]⟩
  have hmem : ι t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    refine Submonoid.subset_closure (And.intro ht fun t' ht' => ?_)
    rw [hfix] at ht'
    have ht'' : t' = ι t := IsFractionRing.injective (𝓞 K) K ht'
    rw [ht'']
    exact ht
  refine ⟨ι t, hmem, ?_⟩
  rw [e]
  exact Submodule.mem_one.mpr ⟨_, rfl⟩

omit hK in

theorem mul_inv_pow_mem {P : Ideal (𝓞 K)} {π : K}
    (h1 : ∀ z ∈ extP K (P.comap ι), Dv (locRing P) π (κ z)) (j : ℕ) :
    ∀ z ∈ extP K (P.comap ι) ^ j, κ z * (π ^ j)⁻¹ ∈ locRing P := by
  have hz0 : ∀ z : 𝓞 K, κ z ∈ locRing P := by
    intro z
    show κ z ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Submodule.mem_one.mpr ⟨z, rfl⟩⟩
  induction j with
  | zero =>
    intro z _
    rw [pow_zero, inv_one, mul_one]
    exact hz0 z
  | succ j ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun u w hu hw => ?_)
    · have hxy := (locRing P).mul_mem (ih x hx) (h1 y hy)
      rw [map_mul, pow_succ, mul_inv]
      convert hxy using 1
      ring
    · rw [map_add, add_mul]
      exact (locRing P).add_mem hu hw

theorem unifVal_at {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧ ∀ a : 𝓞 F, a ≠ 0 →
      IsUnitIn (locRing P) (algebraMap F K (a : F) * (π ^ vF (P.comap ι) a)⁻¹) := by
  obtain ⟨π, hπ, h1, h2⟩ := exists_isUnif hF hP
  have hPm : (P.comap ι).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hcoe : ∀ c : 𝓞 F, algebraMap F K (c : F) = κ (ι c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hstar : ∀ c : 𝓞 F, star (κ (ι c)) = κ (ι c) := fun c => (hF _).mpr ⟨(c : F), hcoe c⟩
  have hπ0 : π ≠ 0 := hπ.3
  have hex : ∃ p0 ∈ P.comap ι, IsUnitIn (locRing P) (κ (ι p0) * π⁻¹) := by
    by_contra hne
    push_neg at hne
    have hle : extP K (P.comap ι) ≤ extP K (P.comap ι) ^ 2 := by
      show Ideal.map ι (P.comap ι) ≤ _
      refine Ideal.map_le_iff_le_comap.mpr fun p0 hp0 => ?_
      show ι p0 ∈ extP K (P.comap ι) ^ 2
      have hmemR : κ (ι p0) * π⁻¹ ∈ locRing P := h1 _ (Ideal.mem_map_of_mem _ hp0)
      have hfix : star (κ (ι p0) * π⁻¹) = κ (ι p0) * π⁻¹ := by
        rw [star_mul', star_inv₀, hπ.2, hstar]
      exact h2 _ ((hπ.4 _ hmemR hfix).resolve_left (hne p0 hp0))
    have hI0 : extP K (P.comap ι) ≠ ⊥ := by
      intro h0
      have hp0 : P.comap ι ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hPm (NumberField.RingOfIntegers.not_isField F)
      apply hp0
      rw [eq_bot_iff]
      intro c hc
      have hc' : ι c ∈ extP K (P.comap ι) := Ideal.mem_map_of_mem _ hc
      rw [h0, Ideal.mem_bot] at hc'
      have hk : algebraMap F K (c : F) = 0 := by rw [hcoe, hc', map_zero]
      rw [Ideal.mem_bot]
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp
        ((map_eq_zero (algebraMap F K)).mp hk)
    have hIT : extP K (P.comap ι) ≠ ⊤ := by
      intro htop
      have hle' : extP K (P.comap ι) ≤ P := Ideal.map_comap_le
      rw [htop] at hle'
      exact hP.ne_top (top_le_iff.mp hle')
    have hsq : extP K (P.comap ι) * extP K (P.comap ι) = extP K (P.comap ι) * ⊤ := by
      rw [Ideal.mul_top]
      refine le_antisymm Ideal.mul_le_right ?_
      rw [← sq]
      exact hle
    exact hIT (mul_left_cancel₀ hI0 hsq)
  obtain ⟨p0, hp0, hu⟩ := hex
  have hu' : κ (ι p0) * π⁻¹ ≠ 0 ∧ κ (ι p0) * π⁻¹ ∈ locRing P ∧
      (κ (ι p0) * π⁻¹)⁻¹ ∈ locRing P := hu
  have hy : κ (ι p0) ≠ 0 := fun h0 => hu'.1 (by rw [h0, zero_mul])
  refine ⟨π, hπ, fun a ha => ?_⟩
  obtain ⟨hav, -⟩ := vF_spec_of_ne_zero hPm ha
  have hκa : κ (ι a) ≠ 0 := jK_iota_ne_zero ha
  rw [hcoe a]
  have hιa : ι a ∈ extP K (P.comap ι) ^ vF (P.comap ι) a := by
    show ι a ∈ (Ideal.map ι (P.comap ι)) ^ _
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hav
  have hxR : κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹ ∈ locRing P :=
    mul_inv_pow_mem hF h1 _ (ι a) hιa
  have hb : p0 ^ vF (P.comap ι) a ∈ P.comap ι ^ vF (P.comap ι) a := Ideal.pow_mem_pow hp0 _
  have hdiv := div_mem_locRing_of_mem_pow hK hF hP ha hb
  have hinvR : ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a ∈ locRing P :=
    (locRing P).pow_mem hu'.2.2 _
  have e : (κ (ι a) * (π ^ vF (P.comap ι) a)⁻¹)⁻¹ =
      ((κ (ι p0) * π⁻¹)⁻¹) ^ vF (P.comap ι) a * (κ (ι (p0 ^ vF (P.comap ι) a)) / κ (ι a)) := by
    rw [map_pow, map_pow, mul_inv, inv_inv, mul_inv, inv_inv, mul_pow, inv_pow, div_eq_mul_inv,
      mul_comm ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹) (π ^ vF (P.comap ι) a), mul_assoc,
      ← mul_assoc ((κ (ι p0) ^ vF (P.comap ι) a)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hy), one_mul,
      mul_comm]
  refine (⟨mul_ne_zero hκa (inv_ne_zero (pow_ne_zero _ hπ0)), hxR, ?_⟩ : _ ∧ _ ∧ _)
  rw [e]
  exact (locRing P).mul_mem hinvR hdiv

end Formalism.L2.SG.Pf.TemperedBoundGL3

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

theorem uniformizer_valuation_holds : G3.UnifVal := by
  intro K F _ _ _ _ _ _ hK hF P hP
  exact unifVal_at hK hF hP

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sums {J : Type} [Fintype J] {b : J → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c d : J → K) :
    h (∑ i, c i • b i) (∑ i, d i • b i) = ∑ i, star (c i) * d i * h (b i) (b i) := by
  rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ₂, G3.form_sum_orth ho d i, starRingEnd_apply, smul_eq_mul, mul_assoc]

theorem sum_filter_smul {J : Type} [Fintype J] (p : J → Prop) [DecidablePred p] (x : J → K)
    (b : J → V) :
    ∑ i ∈ Finset.univ.filter p, x i • b i = ∑ i, (if p i then x i else 0) • b i := by
  simp only [Finset.sum_filter, ite_smul, zero_smul]

private theorem unit_mul_lemma {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) :
    IsUnitIn S (a * b) := by
  obtain ⟨ha0, haS, haI⟩ := ha
  obtain ⟨hb0, hbS, hbI⟩ := hb
  refine (⟨mul_ne_zero ha0 hb0, S.mul_mem haS hbS, ?_⟩ : a * b ≠ 0 ∧ a * b ∈ S ∧ (a * b)⁻¹ ∈ S)
  rw [mul_inv]
  exact S.mul_mem haI hbI

private theorem unit_add_dv_lemma_2 (hπ : IsUnif S π) {u d : K} (hu : IsUnitIn S u) (hd : Dv S π d) :
    IsUnitIn S (u + d) := by
  have hu' : u ≠ 0 ∧ u ∈ S ∧ u⁻¹ ∈ S := hu
  have hd' : d * π⁻¹ ∈ S := hd
  have e : u * (1 + π * (u⁻¹ * (d * π⁻¹))) = u + d := by
    rw [mul_add, mul_one, mul_left_comm u π, mul_inv_cancel_left₀ hu'.1, mul_left_comm π d,
      mul_inv_cancel₀ hπ.3, mul_one]
  rw [← e]
  exact unit_mul_lemma hu (hπ.5 _ (S.mul_mem hu'.2.2 hd'))

theorem rebaseAt_of (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hUP : ∀ (J : Type) [Fintype J] [DecidableEq J] (b : J → V) (e : J → ℕ) (i₀ : J),
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∀ x : J → K, (∀ i, x i ∈ S) →
      IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
        (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧
        (∀ k, e k ≠ e i₀ → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b)
    (hAB : ∀ (J : Type) [Fintype J] [DecidableEq J] (e : J → ℕ) (i₀ : J) (x : J → K),
      (∀ i, x i ∈ S) → ∀ T : Finset J, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : J → V,
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧ (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b) :
    G3.RebaseAt S π h := by
  intro J _ _ b e i₀ ho hu hmin X hX hXu
  obtain ⟨x, hxS, rfl⟩ := hX
  have hπ0 : π ≠ 0 := hπ.3
  have hterm : ∀ i, e i ≠ e i₀ →
      Dv S π (star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹) := by
    intro i hi
    have hlt : e i₀ < e i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
    have hP : π ^ e i ≠ 0 := pow_ne_zero _ hπ0
    have hw : h (b i) (b i) * (π ^ e i)⁻¹ ∈ S := (show _ ∧ _ ∧ _ from hu i).2.1
    have hs : star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) ∈ S :=
      S.mul_mem (S.mul_mem (hS.1 _ (hxS i)) (hxS i)) hw
    have hk : Dv S π (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [← pow_sub₀ π hπ0 (hmin i)]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      show π ^ (e i - e i₀) * π⁻¹ ∈ S
      rw [hm, show e i₀ + m + 1 - e i₀ = m + 1 by omega, pow_succ, mul_inv_cancel_right₀ hπ0]
      exact S.pow_mem hπ.1 m
    have e1 : star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹ =
        star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) * (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [mul_assoc _ (_ * _⁻¹), mul_assoc (h (b i) (b i)), inv_mul_cancel_left₀ hP, ← mul_assoc]
    rw [e1]
    exact Dv.mul_left hk hs
  have hD : Dv S π (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹ -
      h (∑ i, x i • b i) (∑ i, x i • b i) * (π ^ e i₀)⁻¹) := by
    rw [sum_filter_smul, form_sums ho, form_sums ho, ← sub_mul, ← Finset.sum_sub_distrib,
      Finset.sum_mul]
    refine Finset.sum_induction _ (Dv S π) (fun _ _ ha hb => Dv.add ha hb) ?_ fun i _ => ?_
    · show (0 : K) * π⁻¹ ∈ S
      rw [zero_mul]
      exact S.zero_mem
    · by_cases hi : e i = e i₀
      · rw [if_pos hi, sub_self, zero_mul]
        show (0 : K) * π⁻¹ ∈ S
        rw [zero_mul]
        exact S.zero_mem
      · rw [if_neg hi, star_zero, zero_mul, zero_mul, zero_sub, neg_mul]
        exact Dv.neg (hterm i hi)
  have hYu : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) := by
    have e2 : ∀ p q : K, p + (q - p) = q := fun p q => by ring
    have := unit_add_dv_lemma_2 hπ hXu hD
    rwa [e2] at this
  obtain ⟨c, hco, hcu, hci0, hck, hspan, hspanS⟩ := hUP J b e i₀ ho hu x hxS hYu
  have hi₀T : i₀ ∉ Finset.univ.filter (fun j => ¬ e j = e i₀) := fun hm =>
    (Finset.mem_filter.mp hm).2 rfl
  have hTlt : ∀ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), e i₀ < e j := fun j hj =>
    lt_of_le_of_ne (hmin j) (Ne.symm (Finset.mem_filter.mp hj).2)
  obtain ⟨c', hco', hcu', hc'i0, hc'k, hspan', hspanS'⟩ :=
    hAB J e i₀ x hxS _ hi₀T hTlt c hco hcu
  have hT' : ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • c j =
      ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • b j :=
    Finset.sum_congr rfl fun j hj => by rw [hck j (Finset.mem_filter.mp hj).2]
  refine ⟨c', hco', hcu', ?_, hspan'.trans hspan, fun v => (hspanS' v).trans (hspanS v)⟩
  rw [hc'i0, hci0, hT', Finset.sum_filter_add_sum_filter_not]

end

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem sd_basis_bot {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun v => ?_, ?_⟩
  · rw [spanS_empty]
    constructor
    · rintro rfl
      exact M.zero_mem
    · intro hv
      have := hM.le v hv
      rwa [hW, Submodule.mem_bot] at this
  · rw [hW, Set.range_eq_empty, Submodule.span_empty]

theorem sup_cutW {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    K ∙ x ⊔ cutW h W x = W := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) inf_le_left
  · intro w hw
    have e : w = (h x w * (h x x)⁻¹) • x + (w - (h x w * (h x x)⁻¹) • x) := by abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ?_
    refine mem_cutW.mpr ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hxx, mul_one, sub_self]

theorem sd_basis (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  intro n
  induction n with
  | zero =>
    intro W M hn hM
    exact sd_basis_bot hM (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro W M hn hM
    by_cases hbot : W = ⊥
    · exact sd_basis_bot hM hbot
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    have hxW := hM.le x hx
    obtain ⟨k, f, hfo, hfu, hfM, hfW⟩ := ih _ _
      (by have := finrank_cutW_lt (h := h) hxW hu.1; omega) (hM.cut hx hu)
    have hfc : ∀ i, f i ∈ cutW h W x := fun i => by
      rw [← hfW]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfm : ∀ i, f i ∈ M := fun i =>
      (mem_cutM.mp ((hfM (f i)).mp (mem_spanS_self f i))).1
    refine ⟨k + 1, Fin.cons x f, ?_, ?_, fun v => ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_cutW.mp (hfc j)).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using symm_zero hs (mem_cutW.mp (hfc i)).2
        | succ j =>
          simpa using hfo i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hfu i
    · constructor
      · rintro ⟨c, hc, rfl⟩
        refine M.sum_mem fun i _ => hM.smul_mem _ (hc i) _ ?_
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using hfm i
      · intro hv
        obtain ⟨d, hd', hdv⟩ := (hfM _).mpr (proj_mem hM.toIsLatIn hx hu hv)
        refine ⟨Fin.cons (h x v * (h x x)⁻¹) d, fun i => ?_, ?_⟩
        · cases i using Fin.cases with
          | zero => simpa using S.mul_mem (hM.int _ hx _ hv) hu.2.2
          | succ i => simpa using hd' i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hdv]
          abel
    · rw [Fin.range_cons, Submodule.span_insert, hfW]
      exact sup_cutW hxW hu.1

end

end Formalism.L2.SG.Pf.G3
end
end

section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

private theorem mem_iff_lemma {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

private theorem smul_mem_lemma_2 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {a : K} (ha : a ∈ S)
    {v : V} (hv : v ∈ spanS S g) : a • v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  exact ⟨fun i => a * d i, fun i => S.mul_mem ha (hd i), by simp [Finset.smul_sum, mul_smul]⟩

private theorem spanS_le_lemma_3 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  exact AddSubgroup.sum_mem _ fun k _ => smul_mem_lemma_2 (hc k) (hfg k)

private theorem mem_span_lemma_4 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] {g : ι → V} {v : V}
    (hv : v ∈ spanS S g) : v ∈ Submodule.span K (Set.range g) := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem spans_eq_lemma_5 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V}
    {g : ι → V} (h1 : ∀ k, f k ∈ spanS S g) (h2 : ∀ i, g i ∈ spanS S f) :
    Submodule.span K (Set.range f) = Submodule.span K (Set.range g) ∧
      ∀ v, v ∈ spanS S f ↔ v ∈ spanS S g := by
  refine ⟨le_antisymm ?_ ?_, fun v => ⟨spanS_le_lemma_3 h1, spanS_le_lemma_3 h2⟩⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact mem_span_lemma_4 (h1 k)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_lemma_4 (h2 i)

private theorem linInd_lemma_6 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} {f : ι → V} (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0)
    (hn : ∀ i, h (f i) (f i) ≠ 0) : LinearIndependent K f := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 := congrArg (h (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro h'
    exact absurd hi h'

private theorem form_sum_lemma_7 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) (a c : ι → K) :
    h (∑ i, a i • b i) (∑ j, c j • b j) = ∑ i, star (a i) * c i * h (b i) (b i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  · intro j _ hji
    rw [map_smulₛₗ, LinearMap.smul_apply, ho j i hji, smul_zero]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

private theorem mem_self_lemma_9 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {S : Subring K} {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

private theorem isSD_lemma_8 {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    {S : Subring K} (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} {ι : Type} [Fintype ι]
    [DecidableEq ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i))) :
    IsSD S h (Submodule.span K (Set.range b)) (spanS S b) where
  le := fun m hm => mem_span_lemma_4 hm
  smul_mem := fun a ha m hm => smul_mem_lemma_2 ha hm
  int := by
    intro x hx y hy
    rw [mem_iff_lemma] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    rw [form_sum_lemma_7 ho]
    exact sum_mem fun i _ => S.mul_mem (S.mul_mem (hS.star_mem _ (ha i)) (hc i)) (hu i).2.1
  span := by
    intro x hx
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    choose T hTS hT0 hTg using fun i => hS.frac (g i)
    refine ⟨∏ i, T i, Finset.prod_ne_zero_iff.2 fun i _ => hT0 i, ?_⟩
    rw [mem_iff_lemma]
    refine ⟨fun i => (∏ j, T j) * g i, fun i => ?_, ?_⟩
    · dsimp only
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
      exact S.mul_mem (S.prod_mem fun j _ => hTS j) (hTg i)
    · rw [Finset.smul_sum]
      simp only [smul_smul]
  dual := by
    intro x hx hdual
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    rw [mem_iff_lemma]
    refine ⟨g, fun i => ?_, rfl⟩
    have h1 := hdual (b i) (mem_self_lemma_9 b i)
    rw [map_sum, Finset.sum_eq_single i] at h1
    · rw [map_smul, smul_eq_mul] at h1
      have h2 := S.mul_mem h1 (hu i).2.2
      rwa [mul_assoc, mul_inv_cancel₀ (hu i).1, mul_one] at h2
    · intro j _ hji
      rw [map_smul, ho i j (Ne.symm hji), smul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'

theorem uni_part {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    {e : ι → ℕ} {i₀ : ι} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) (x : ι → K) (hx : ∀ i, x i ∈ S)
    (hX : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧ (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
      c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧ (∀ k, e k ≠ e i₀ → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  set Xs := ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i with hXs
  have hπ0 : π ≠ 0 := hπ.ne
  have hp0 : π ^ e i₀ ≠ 0 := pow_ne_zero _ hπ0
  obtain ⟨h', hh'⟩ : ∃ h' : V →ₗ⋆[K] V →ₗ[K] K, ∀ v w, h' v w = (π ^ e i₀)⁻¹ * h v w :=
    ⟨(π ^ e i₀)⁻¹ • h, fun v w => by simp only [LinearMap.smul_apply, smul_eq_mul]⟩
  have hstar : ∀ v w, star (h v w) = h w v := fun v w => by
    rw [← starRingEnd_apply]
    exact hs.eq v w
  have hpstar : star ((π ^ e i₀)⁻¹) = (π ^ e i₀)⁻¹ := by rw [star_inv₀, star_pow, hπ.fix]
  have hs' : h'.IsSymm := LinearMap.IsSymm.mk fun v w => by
    rw [hh', hh', starRingEnd_apply, star_mul, hstar, hpstar, mul_comm]
  have hz : ∀ v w, h' v w = 0 → h v w = 0 := fun v w hvw => by
    rw [hh'] at hvw
    exact (mul_eq_zero.1 hvw).resolve_left (inv_ne_zero hp0)
  have hd' : ∀ v, h' v v = 0 → v = 0 := fun v hv => hd v (hz v v hv)
  have hconv : ∀ v, h' v v = h v v * (π ^ e i₀)⁻¹ := fun v => by rw [hh', mul_comm]
  obtain ⟨bP, hbP⟩ : ∃ bP : {i // e i = e i₀} → V, ∀ p, bP p = b p := ⟨fun p => b p, fun _ => rfl⟩
  have hoP : ∀ p q, p ≠ q → h' (bP p) (bP q) = 0 := fun p q hpq => by
    rw [hh', hbP, hbP, ho _ _ (fun hq => hpq (Subtype.ext hq)), mul_zero]
  have huP : ∀ p, IsUnitIn S (h' (bP p) (bP p)) := fun p => by
    rw [hconv, hbP]
    have := hu p
    rwa [p.2] at this
  have hSD := isSD_lemma_8 hS hoP huP
  have hXeq : Xs = ∑ p : {i // e i = e i₀}, x p • bP p := by
    simp only [hbP]
    exact Finset.sum_subtype _ (fun i => by simp) (fun i => x i • b i)
  have hXL : Xs ∈ spanS S bP := (mem_iff_lemma _ _).2 ⟨fun p => x p, fun p => hx p, hXeq⟩
  have hXu' : IsUnitIn S (h' Xs Xs) := by
    rw [hconv]
    exact hX
  have hXX : h' Xs Xs ≠ 0 := hXu'.1
  have hX0 : Xs ≠ 0 := fun h0 => hXX (by rw [h0, map_zero])
  have hXW : Xs ∈ Submodule.span K (Set.range bP) := mem_span_lemma_4 hXL
  obtain ⟨k, f, hof, huf, hspf, hspanf⟩ := sd_basis hS hπ hs' hd' _
    (cutW h' (Submodule.span K (Set.range bP)) Xs) (cutM h' (spanS S bP) Xs) le_rfl
    (hSD.cut hXL hXu')
  have hinf : K ∙ Xs ⊓ cutW h' (Submodule.span K (Set.range bP)) Xs = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv1
    have hv2' : t • Xs ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hv2
    have ht := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv2').2
    rw [map_smul, smul_eq_mul] at ht
    rw [(mul_eq_zero.1 ht).resolve_right hXX, zero_smul]
    exact Submodule.zero_mem _
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ Xs)
    (cutW h' (Submodule.span K (Set.range bP)) Xs)
  rw [sup_cutW hXW hXX, hinf, finrank_bot, finrank_span_singleton hX0, ← hspanf,
    finrank_span_eq_card (linInd_lemma_6 hof (fun j => (huf j).1)),
    finrank_span_eq_card (linInd_lemma_6 hoP (fun p => (huP p).1)), Fintype.card_fin] at e1
  set p₀ : {i // e i = e i₀} := ⟨i₀, rfl⟩ with hp₀
  have hQ : Fintype.card {p : {i // e i = e i₀} // p ≠ p₀} = k := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  let σ := Fintype.equivFinOfCardEq hQ
  obtain ⟨gP, hg0, hgq⟩ : ∃ gP : {i // e i = e i₀} → V, gP p₀ = Xs ∧
      ∀ q : {p : {i // e i = e i₀} // p ≠ p₀}, gP q.1 = f (σ q) :=
    ⟨fun p => if hp : p = p₀ then Xs else f (σ ⟨p, hp⟩), dif_pos rfl, fun q => dif_neg q.2⟩
  obtain ⟨c, hcP, hcn⟩ : ∃ c : ι → V, (∀ p : {i // e i = e i₀}, c p = gP p) ∧
      ∀ i, e i ≠ e i₀ → c i = b i :=
    ⟨fun i => if hi : e i = e i₀ then gP ⟨i, hi⟩ else b i, fun p => dif_pos p.2,
      fun i hi => dif_neg hi⟩
  have hc0 : c i₀ = Xs := (hcP p₀).trans hg0
  have hXf : ∀ j, h Xs (f j) = 0 := fun j => by
    have hm : f j ∈ cutW h' (Submodule.span K (Set.range bP)) Xs := by
      rw [← hspanf]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hm' : f j ∈ Submodule.span K (Set.range bP) ⊓ LinearMap.ker (h' Xs) := hm
    exact hz _ _ (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hm').2)
  have hfX : ∀ j, h (f j) Xs = 0 := fun j => by rw [← hstar, hXf, star_zero]
  have hgo : ∀ p p' : {i // e i = e i₀}, p ≠ p' → h (gP p) (gP p') = 0 := by
    intro p p' hpp
    by_cases hp : p = p₀
    · have hp' : p' ≠ p₀ := fun hq => hpp (hp.trans hq.symm)
      rw [hp, hg0, show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
      exact hXf _
    · by_cases hp' : p' = p₀
      · rw [hp', hg0, show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
        exact hfX _
      · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩,
          show gP p' = f (σ ⟨p', hp'⟩) from hgq ⟨p', hp'⟩]
        exact hz _ _ (hof _ _ (fun hq => hpp (congrArg Subtype.val (σ.injective hq))))
  have hfL : ∀ j, f j ∈ spanS S bP := fun j => (mem_cutM.1 ((hspf _).1 (mem_self_lemma_9 f j))).1
  have hgL : ∀ p, gP p ∈ spanS S bP := fun p => by
    by_cases hp : p = p₀
    · rw [hp, hg0]
      exact hXL
    · rw [show gP p = f (σ ⟨p, hp⟩) from hgq ⟨p, hp⟩]
      exact hfL _
  have hperp : ∀ w ∈ Submodule.span K (Set.range bP), ∀ j, e j ≠ e i₀ →
      h w (b j) = 0 ∧ h (b j) w = 0 := by
    intro w hw j hj
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    have hne : ∀ p : {i // e i = e i₀}, (p : ι) ≠ j := fun p hq => hj (hq ▸ p.2)
    constructor
    · rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun p _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, hbP, ho _ _ (hne p), smul_zero]
    · rw [map_sum]
      exact Finset.sum_eq_zero fun p _ => by
        rw [map_smul, hbP, ho _ _ (hne p).symm, smul_zero]
  have hoc : ∀ i j, i ≠ j → h (c i) (c j) = 0 := by
    intro i j hij
    by_cases hi : e i = e i₀
    · by_cases hj : e j = e i₀
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact hgo _ _ (fun hq => hij (congrArg Subtype.val hq))
      · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hcn j hj]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) j hj).1
    · rw [hcn i hi]
      by_cases hj : e j = e i₀
      · rw [show c j = gP ⟨j, hj⟩ from hcP ⟨j, hj⟩]
        exact (hperp _ (mem_span_lemma_4 (hgL _)) i hi).2
      · rw [hcn j hj]
        exact ho i j hij
  have huc : ∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹) := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩, hi, ← hconv]
      by_cases hp : (⟨i, hi⟩ : {i // e i = e i₀}) = p₀
      · rw [hp, hg0]
        exact hXu'
      · rw [show gP ⟨i, hi⟩ = f (σ ⟨⟨i, hi⟩, hp⟩) from hgq ⟨⟨i, hi⟩, hp⟩]
        exact huf _
    · rw [hcn i hi]
      exact hu i
  have h1 : ∀ i, c i ∈ spanS S b := by
    intro i
    by_cases hi : e i = e i₀
    · rw [show c i = gP ⟨i, hi⟩ from hcP ⟨i, hi⟩]
      exact spanS_le_lemma_3 (fun p => by rw [hbP]; exact mem_self_lemma_9 b p) (hgL _)
    · rw [hcn i hi]
      exact mem_self_lemma_9 b i
  have hfc : ∀ j, f j ∈ spanS S c := fun j => by
    have hfj : f j = c (σ.symm j).1.1 := by rw [hcP, hgq, Equiv.apply_symm_apply]
    rw [hfj]
    exact mem_self_lemma_9 c _
  have h2 : ∀ i, b i ∈ spanS S c := by
    intro i
    by_cases hi : e i = e i₀
    · have hbi : b i ∈ spanS S bP := by
        have hm := mem_self_lemma_9 (S := S) bP ⟨i, hi⟩
        rwa [hbP] at hm
      have hr := (hspf _).2 (proj_mem hSD.toIsLatIn hXL hXu' hbi)
      have ha : h' Xs (b i) * (h' Xs Xs)⁻¹ ∈ S := S.mul_mem (hSD.int _ hXL _ hbi) hXu'.2.2
      have key : b i = (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs
          + (b i - (h' Xs (b i) * (h' Xs Xs)⁻¹) • Xs) := by abel
      rw [key]
      refine add_mem (smul_mem_lemma_2 ha ?_) (spanS_le_lemma_3 hfc hr)
      rw [← hc0]
      exact mem_self_lemma_9 c i₀
    · rw [← hcn i hi]
      exact mem_self_lemma_9 c i
  obtain ⟨hspc, hiffc⟩ := spans_eq_lemma_5 h1 h2
  exact ⟨c, hoc, huc, hc0, hcn, hspc, hiffc⟩

end Formalism.L2.SG.Pf.G3
end
end

section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem rebasing_holds : G3.Rebase := by
  intro K V _ _ _ _ _ S π h hS hπ hs hd
  exact rebaseAt_of hS hπ
    (fun J _ _ b e i₀ ho hu x hx hX => G3.uni_part hS hπ hs hd ho hu x hx hX)
    (fun J _ _ e i₀ x hx T hT hlt b ho hu => G3.absorb hS hπ hs x hx T hT hlt b ho hu)

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have hsp := hJ K F V L hLl _ h𝔭 _ b hbL
  have hsp' := hJ K F V L' hLl' _ h𝔭 _ b' hbL'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
end
end
