import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zmult_of_span (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hnx m
    · rw [mul_smul]; exact zsmul_mem hmy n
  | smul a x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, α, hα⟩ := Formalism.HermitianLatticesTheory.traceReal_den a
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : (k * n) • (a • x) = α • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul K (k * n), ← algebraMap_smul K α (n • x),
        ← Int.cast_smul_eq_zsmul K n, smul_smul, smul_smul]
      congr 1
      rw [show algebraMap (NumberField.RingOfIntegers K) K α = (α : K) from rfl, ← hα]
      push_cast
      ring
    rw [e1]
    exact M.smul_mem α hnx

def zdiv (B : Submodule (𝓞 K) V) (n : ℤ) : Submodule (𝓞 K) V where
  carrier := {x | n • x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show n • (a + b) ∈ B
    rw [smul_add]
    exact B.add_mem ha hb
  smul_mem' := by
    intro c x hx
    show n • (c • x) ∈ B
    rw [smul_comm]
    exact B.smul_mem c hx

theorem exists_zsmul_of_fg {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ y ∈ A, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! m hm hmy using fun y (hy : y ∈ S) => hAB y (Submodule.subset_span hy)
  refine ⟨∏ y ∈ S, m y, Finset.prod_ne_zero_iff.2 hm, fun x hx => ?_⟩
  show x ∈ zdiv B (∏ y ∈ S, m y)
  refine (Submodule.span_le.2 ?_) hx
  intro y hy
  show (∏ y ∈ S, m y) • y ∈ B
  rw [← Finset.prod_erase_mul S m hy, mul_smul]
  exact zsmul_mem (hmy y hy) _

theorem locF_le_of_zsmul {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx

theorem badFinite : BadFinite := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF Λ₀ hΛ₀ U M hM
  classical
  set N : Submodule (𝓞 K) V := Λ₀ ⊓ U.restrictScalars (𝓞 K) with hN
  have hMU : ∀ y ∈ M, y ∈ U := fun y hy => by
    rw [← hM.2]; exact Submodule.subset_span hy
  obtain ⟨n₁, hn₁, h₁⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ M, n • x ∈ N := by
    refine exists_zsmul_of_fg hM.1 fun y hy => ?_
    obtain ⟨m, hm, hmy⟩ := Formalism.HermitianLatticesTheory.traceReal_mult Λ₀ hΛ₀ y
    exact ⟨m, hm, Submodule.mem_inf.2 ⟨hmy, zsmul_mem (hMU y hy) m⟩⟩
  have hNfg : N.FG := Submodule.FG.of_le hΛ₀.fg inf_le_left
  obtain ⟨n₂, hn₂, h₂⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ N, n • x ∈ M := by
    refine exists_zsmul_of_fg hNfg fun y hy => zmult_of_span M y ?_
    rw [hM.2]
    exact (Submodule.mem_inf.1 hy).2
  set a : 𝓞 F := ((n₁ * n₂ : ℤ) : 𝓞 F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Int.cast_ne_zero]
    exact mul_ne_zero hn₁ hn₂
  have hD : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | a ∈ 𝔭.1}.Finite := by
    refine ((Ideal.finite_factors hD).image (fun v =>
      (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
    intro 𝔭 h𝔭
    have hne : 𝔭.1 ≠ ⊥ := fun e => ha0 (by
      have : a ∈ 𝔭.1 := h𝔭
      rwa [e, Ideal.mem_bot] at this)
    refine ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, ?_, rfl⟩
    show 𝔭.1 ∣ Ideal.span {a}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
  have haP : a ∉ 𝔭.1 := fun h => h𝔭 (hfin.mem_toFinset.2 h)
  have e : a = (n₁ : 𝓞 F) * (n₂ : 𝓞 F) := by rw [ha]; push_cast; ring
  have h1P : (n₁ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_right _ _ h)
  have h2P : (n₂ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_left _ _ h)
  exact le_antisymm (locF_le_of_zsmul 𝔭.2.isPrime n₂ h2P h₂)
    (locF_le_of_zsmul 𝔭.2.isPrime n₁ h1P h₁)

theorem glueExists_of_local (hloc : GlueLocal) : GlueExists :=
  glueExists_of_of hloc badFinite

end Formalism.L2.SG.Pf.G7
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.FamilyMeetLattice

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

theorem alg_eq {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (t : 𝓞 F) : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K t).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F K t)
    | simp

theorem family_meet_holds : FamMeet := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  classical
  obtain ⟨hbU, hspan, -, -, -⟩ := hba
  obtain ⟨hwW, hworth, hwc, hτ, ⟨s₀, hu⟩, -, -⟩ := hg
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro e0
    exact hu.notMem (by rw [show π = 0 from RingOfIntegers.ext e0]; exact Ideal.zero_mem _)
  set p := algebraMap F K (π : F) with hp
  set G := glueFam K 𝔭 b a π w τ with hG
  have hGl : ∀ i, G (Sum.inl i) = if vF 𝔭 (a i) = 0 then b i else
      ((p)⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i)) := fun i => rfl
  have hGr : ∀ j, G (Sum.inr j) = w j := fun j => rfl
  have hUloc : locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
    Formalism.L2.SG.Pf.G7.locF_subspace U h𝔭.isPrime
  apply le_antisymm
  ·
    rintro x ⟨hx, hxU⟩
    rw [← hspan]
    obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
    refine (LocF.mem_locF_iff h𝔭.isPrime _ x).2 ⟨t, ht, ?_⟩
    set y := algebraMap (𝓞 F) (𝓞 K) t • x with hy
    have hyU : y ∈ U := Submodule.smul_of_tower_mem U _ hxU
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    let cf : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then algebraMap (𝓞 K) K (γ (Sum.inl i)) else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    let co : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then 0 else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    have hz : y - ∑ i, cf i • b i = ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j := by
      rw [← hγ, Fintype.sum_sum_type, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [hGl, ← algebraMap_smul K (γ (Sum.inl i))]
        simp only [cf, co]
        split_ifs with he
        · rw [zero_smul, sub_self]
        · rw [smul_smul, smul_add]
          abel
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hGr, ← algebraMap_smul K (γ (Sum.inr j))]
    have hzW : ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j ∈ orthK h U :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW _))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hwW _))
    have hzU : y - ∑ i, cf i • b i ∈ U :=
      Submodule.sub_mem _ hyU (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbU i))
    have hz0 : y - ∑ i, cf i • b i = 0 :=
      (Submodule.disjoint_def.1 hUc.disjoint) _ hzU (hz ▸ hzW)
    have hint : ∀ i, vF 𝔭 (a i) ≠ 0 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = cf i := by
      intro i hi
      have h0 := congrArg (h (w (τ i))) (hz.symm.trans hz0)
      rw [map_zero, map_add, map_sum, map_sum] at h0
      simp only [LinearMap.map_smul, smul_eq_mul] at h0
      rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at h0
      · have hc := hwc (τ i)
        rw [hc.1, ← add_mul] at h0
        have hc0 : algebraMap F K (c (τ i)) ≠ 0 := by rw [map_ne_zero]; exact hc.2
        have h1 := (mul_eq_zero.1 h0).resolve_right hc0
        refine ⟨-γ (Sum.inr (τ i)), ?_⟩
        simp only [cf, co, if_neg hi] at h1 ⊢
        rw [map_neg]
        linear_combination -h1
      · intro j _ hj
        rw [hworth _ _ (Ne.symm hj), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro i' _ hi'
        simp only [co]
        split_ifs with he
        · rw [zero_mul]
        · rw [hworth _ _ (fun e => hi' (hτ i' i he hi e.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [sub_eq_zero.1 hz0]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases he : vF 𝔭 (a i) = 0
    · have : cf i = algebraMap (𝓞 K) K (γ (Sum.inl i)) := if_pos he
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · obtain ⟨r, hr⟩ := hint i he
      rw [← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ·
    rw [← hspan]
    refine le_inf (LocF.locF_mono 𝔭 ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases he : vF 𝔭 (a i) = 0
      · have : G (Sum.inl i) = b i := by rw [hGl, if_pos he]
        exact Submodule.subset_span ⟨Sum.inl i, this⟩
      · have e1 : b i = algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i) • G (Sum.inl i) - G (Sum.inr (τ i)) := by
          rw [hGl, if_neg he, hGr, ← algebraMap_smul K, map_pow, alg_eq, smul_smul, ← mul_pow,
            mul_inv_cancel₀ hπ0, one_pow, one_smul, add_sub_cancel_right]
        rw [e1]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.subset_span ⟨_, rfl⟩)
    · calc locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤ locF 𝔭 (U.restrictScalars (𝓞 K)) :=
            LocF.locF_mono 𝔭 (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbU i))
        _ = U.restrictScalars (𝓞 K) := hUloc

end Formalism.L2.SG.Pf.FamilyMeetLattice
end
end

section
namespace Formalism.L2.SG.Pf.Cnt

theorem glueExists_of (hloc : Formalism.L2.SG.Pf.G7.GlueLocal) : GlueExists :=
  Formalism.L2.SG.Pf.G7.glueExists_of_local hloc

theorem glueExists_of_fam (hJ : JordanExists) (hV : Formalism.L2.SG.Pf.GluingBases.GlueVecs)
    (h0 : Formalism.L2.SG.Pf.GluingBases.FamTop) (h1 : Formalism.L2.SG.Pf.GluingBases.FamGram) (h2 : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of (Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam hJ hV h0 h1 h2 Formalism.L2.SG.Pf.FamilyMeetLattice.family_meet_holds)

end Formalism.L2.SG.Pf.Cnt
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem family_gram_holds : FamGram := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hwW j) (b i)) (hbU i))
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => by
    rw [← hs.eq (b i) (w j), hbw]; simp
  have hcP : ∀ i, vF 𝔭 (a i) ≠ 0 → InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K (c (τ i))) := by
    intro i hi
    have h1 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i))) :=
      (hcong i hi).mono (by omega)
    have h2 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : 𝓞 F) : F)) := inP_vF h𝔭 (ha0 i)
    have e : algebraMap F K (c (τ i)) =
        algebraMap F K ((a i : F) + c (τ i)) + -algebraMap F K ((a i : 𝓞 F) : F) := by
      rw [map_add]; ring
    rw [e]; exact h1.add h2.neg
  have hcS : ∀ j, algebraMap F K (c j) ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      exact (hcP i hi).mem_SP
    · push Not at hj
      exact (hunit j fun i hi => hj i hi).1
  have haS : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ∈ SP K 𝔭 := fun i => by
    rw [← jι_eq']; exact jK_mem_SP _
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) = algebraMap F K ((a i : F) + c (τ i)) := by
    intro i
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring
  have key_ik : ∀ i k, i ≠ k → vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 →
      h (b i + w (τ i)) (b k + w (τ k)) = 0 := by
    intro i k hik hi hk
    have hτik : τ i ≠ τ k := fun e => hik (hτ i k hi hk e)
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbo i k hik, hwo _ _ hτik]
    ring
  suffices H : ∀ x y, h (glueFam K 𝔭 b a π w τ x) (glueFam K 𝔭 b a π w τ y) ∈ SP K 𝔭 by
    intro x y; rw [← mem_SP_iff_locF]; exact H x y
  rintro (i | j) (k | l)
  · simp only [glueFam, Sum.elim_inl]
    by_cases hik : i = k
    · subst hik
      by_cases hi : vF 𝔭 (a i) = 0
      · rw [if_pos hi, hbn]; exact haS i
      · rw [if_neg hi, form_smul_smul, key_ii i, star_inv_pow hF, ← pow_add, ← two_mul]
        exact mem_SP_of_inP hu (hcong i hi)
    · by_cases hi : vF 𝔭 (a i) = 0 <;> by_cases hk : vF 𝔭 (a k) = 0
      · rw [if_pos hi, if_pos hk, hbo i k hik]; exact (SP K 𝔭).zero_mem
      · rw [if_pos hi, if_neg hk, form_smul_right, map_add, hbo i k hik, hbw, add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_pos hk, form_smul_left, map_add, LinearMap.add_apply, hbo i k hik, hwb,
          add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_neg hk, form_smul_smul, key_ik i k hik hi hk, mul_zero]
        exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [if_pos hi, hbw]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hi, form_smul_left, map_add, LinearMap.add_apply, hbw, zero_add, star_inv_pow hF]
      by_cases hj : τ i = l
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP i hi)
      · rw [hwo _ _ hj, mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hk : vF 𝔭 (a k) = 0
    · rw [if_pos hk, hwb]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hk, form_smul_right, map_add, hwb, zero_add]
      by_cases hj : τ k = j
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP k hk)
      · rw [hwo _ _ (Ne.symm hj), mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inr]
    by_cases hjl : j = l
    · subst hjl; rw [hwn1]; exact hcS j
    · rw [hwo _ _ hjl]; exact (SP K 𝔭).zero_mem

end Formalism.L2.SG.Pf.GluingBases
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem bin_step_gen (h : V →ₗ⋆[K] V →ₗ[K] K) (hz : ∀ x y, h x y = 0 → h y x = 0) (e₁ e₂ : V)
    (a b x y n : K) (h12 : h e₁ e₂ = 0) (h11 : h e₁ e₁ = a) (h22 : h e₂ e₂ = b) (ha : star a = a)
    (hb : star b = b) (hxy : a * (x * star x) + b * (y * star y) = n) :
    h (x • e₁ + y • e₂) (x • e₁ + y • e₂) = n ∧
      h (x • e₁ + y • e₂) ((star y * b) • e₁ - (star x * a) • e₂) = 0 ∧
      h ((star y * b) • e₁ - (star x * a) • e₂) ((star y * b) • e₁ - (star x * a) • e₂) =
        a * b * n := by
  have h21 : h e₂ e₁ = 0 := hz _ _ h12
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    linear_combination hxy
  · simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    ring
  · simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22, star_mul', star_star, ha, hb]
    linear_combination (a * b) * hxy

theorem TotPos.ne_zero' {x : K} (hx : TotPos x) : x ≠ 0 := by
  intro h0
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hx φ
  rw [h0, map_zero] at this
  simp at this

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem exists_presc_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ x y, star (h x y) = h y x)
    (hpos : ∀ x, x ≠ 0 → TotPos (h x x)) :
    ∀ k : ℕ, k + 1 ≤ finrank K V → ∀ t : Fin (k + 1) → K, (∀ i, star (t i) = t i) →
      (∀ i, TotPos (t i)) →
      ∃ v : Fin (k + 1) → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        (∀ i, i ≠ Fin.last k → h (v i) (v i) = t i) ∧ v (Fin.last k) ≠ 0 := by
  have hz : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hsym, e, star_zero]
  intro k
  induction k with
  | zero =>
    intro hk t _ _
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsub : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
    exact ⟨fun _ => x, fun i j hij => absurd (hsub i j) hij,
      fun i hi => absurd (hsub i _) hi, hx⟩
  | succ k ih =>
    intro hk t hts htp
    obtain ⟨v, ho, h1, hl⟩ := ih (by omega) (fun i => t (Fin.castSucc i)) (fun i => hts _)
      (fun i => htp _)
    obtain ⟨z, hz0, hzv⟩ := GramDeterminantPositive.exists_ortho_ne_zero h v (by omega)
    obtain ⟨x, y, hxy⟩ := hermRepUnram K hK (h (v (Fin.last k)) (v (Fin.last k))) (h z z)
      (t (Fin.castSucc (Fin.last k))) (hsym _ _) (hsym _ _) (hts _) (hpos _ hl) (hpos _ hz0) (htp _)
    obtain ⟨b1, b2, b3⟩ := bin_step_gen h hz (v (Fin.last k)) z _ _ x y _ (hzv _) rfl rfl
      (hsym _ _) (hsym _ _) hxy
    set a := h (v (Fin.last k)) (v (Fin.last k)) with ha
    set b := h z z with hb
    set f₁ := x • v (Fin.last k) + y • z with hf₁
    set f₂ := (star y * b) • v (Fin.last k) - (star x * a) • z with hf₂
    have hf₂0 : f₂ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at b3
      exact mul_ne_zero (mul_ne_zero (TotPos.ne_zero' (hpos _ hl)) (TotPos.ne_zero' (hpos _ hz0)))
        (TotPos.ne_zero' (htp _)) b3.symm
    have c1 : ∀ i, i ≠ Fin.last k → h (v i) f₁ = 0 := by
      intro i hi
      rw [hf₁, map_add, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, add_zero]
    have c2 : ∀ i, i ≠ Fin.last k → h (v i) f₂ = 0 := by
      intro i hi
      rw [hf₂, map_sub, map_smul, map_smul, ho i _ hi, hzv i, smul_zero, smul_zero, sub_zero]
    let u : Fin (k + 1) → V := Function.update v (Fin.last k) f₁
    have ul : u (Fin.last k) = f₁ := Function.update_self _ _ _
    have un : ∀ i, i ≠ Fin.last k → u i = v i := fun i hi => Function.update_of_ne hi _ _
    have uo : ∀ i j, i ≠ j → h (u i) (u j) = 0 := by
      intro i j hij
      by_cases hi : i = Fin.last k
      · have hj : j ≠ Fin.last k := fun e => hij (hi.trans e.symm)
        rw [hi, ul, un j hj]
        exact hz _ _ (c1 j hj)
      · by_cases hj : j = Fin.last k
        · rw [hj, ul, un i hi]; exact c1 i hi
        · rw [un i hi, un j hj]; exact ho i j hij
    have u1 : ∀ i, h (u i) (u i) = t (Fin.castSucc i) := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b1
      · rw [un i hi]; exact h1 i hi
    have u2 : ∀ i, h (u i) f₂ = 0 := by
      intro i
      by_cases hi : i = Fin.last k
      · rw [hi, ul]; exact b2
      · rw [un i hi]; exact c2 i hi
    refine ⟨Fin.snoc u f₂, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hz _ _ (u2 j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact u2 i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact uo i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hi; exact absurd rfl hi
      · intro _
        rw [Fin.snoc_castSucc]; exact u1 i
    · rw [Fin.snoc_last]; exact hf₂0

end Formalism.L2.SG.Pf.GluingBases
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem card_filter_lt_inj {n : ℕ} (P : Finset (Fin n)) {i k : Fin n} (hi : i ∈ P) (hk : k ∈ P)
    (e : (P.filter (· < i)).card = (P.filter (· < k)).card) : i = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (P.filter (· < i)).card < (P.filter (· < k)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hi, h⟩)
        simp at this
    omega
  · have : (P.filter (· < k)).card < (P.filter (· < i)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hk, h⟩)
        simp at this
    omega

theorem card_filter_lt_lt {n : ℕ} (P : Finset (Fin n)) {i : Fin n} (hi : i ∈ P) :
    (P.filter (· < i)).card < P.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, hi, lt_irrefl i⟩)

end Formalism.L2.SG.Pf.GluingBases
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

section
namespace Formalism.L2.SG.Pf.GluingBases

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueVecs_of_last (hL : LastUnit) : GlueVecs :=
  glueVecs_of gluing_vectors_exist (lastRescale_of hL)

end Formalism.L2.SG.Pf.GluingBases

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last_dual (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) (hD : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of_fam jordan_splitting_exists (Formalism.L2.SG.Pf.GluingBases.glueVecs_of_last hL)
    Formalism.L2.SG.Pf.GluingBases.family_top_holds Formalism.L2.SG.Pf.GluingBases.family_gram_holds hD

end Formalism.L2.SG.Pf.Cnt
end

section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem form_sum_orth {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι' → V)
    (hvo : ∀ i k, i ≠ k → h (v i) (v k) = 0) (i : ι') (x : ι' → K) :
    h (v i) (∑ k, x k • v k) = x i * h (v i) (v i) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hvo i k (Ne.symm hk), mul_zero]) (by simp)

theorem form_sum_zero {ι' : Type} [Fintype ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (v : ι' → V)
    (h0 : ∀ k, h u (v k) = 0) (x : ι' → K) : h u (∑ k, x k • v k) = 0 := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, h0, mul_zero, Finset.sum_const_zero]

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  have htop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => GluedFormOrthogonality.form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => GluedFormOrthogonality.form_orth_U hs (hbU i) (hwW j)
  have hϖ0 : algebraMap F K (π : F) ≠ 0 := by rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  set L := Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)) with hL
  have hGi : ∀ s, glueFam K 𝔭 b a π w τ s ∈ L := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hGw : ∀ j, w j ∈ L := fun j => hGi (Sum.inr j)
  have hg1 : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hg0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have hGb : ∀ i, b i ∈ L := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [← hg0 i hi]; exact hGi _
    · have e : b i = (algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i)) • glueFam K 𝔭 b a π w τ (Sum.inl i)
          - w (τ i) := by
        rw [hg1 i hi, ← algebraMap_smul K, smul_smul, map_pow, jι_eq', ← mul_pow,
          mul_inv_cancel₀ hϖ0, one_pow, one_smul, add_sub_cancel_right]
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hGi _)) (hGw _)
  intro x hx
  have hX : ∀ z ∈ L, h z x ∈ SP K 𝔭 := fun z hz => by
    rw [mem_SP_iff_locF]; exact hx z (LocF.le_locF 𝔭 _ hz)
  have hbw_top : Submodule.span K (Set.range (Sum.elim b w)) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rcases s with i | j
    · by_cases hi : vF 𝔭 (a i) = 0
      · rw [hg0 i hi]; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · rw [hg1 i hi]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inr (τ i), rfl⟩))
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hxmem : x ∈ Submodule.span K (Set.range (Sum.elim b w)) := by
    rw [hbw_top]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxmem
  rw [Fintype.sum_sum_type] at hf
  simp only [Sum.elim_inl, Sum.elim_inr] at hf
  have hbx : ∀ i, h (b i) x = f (Sum.inl i) * algebraMap F K (a i : F) := by
    intro i
    rw [← hf, map_add, form_sum_orth h b hbo i, form_sum_zero h (b i) w (hbw i), hbn, add_zero]
  have hwx : ∀ j, h (w j) x = f (Sum.inr j) * algebraMap F K (c j) := by
    intro j
    rw [← hf, map_add, form_sum_orth h w hwo j, form_sum_zero h (w j) b (fun i => hwb i j),
      (hwn j).1, zero_add]
  have hα : ∀ i, f (Sum.inl i) * algebraMap F K (a i : F) ∈ SP K 𝔭 := fun i => by
    rw [← hbx]; exact hX _ (hGb i)
  have hγ : ∀ j, f (Sum.inr j) * algebraMap F K (c j) ∈ SP K 𝔭 := fun j => by
    rw [← hwx]; exact hX _ (hGw j)
  have hσ : ∀ i, vF 𝔭 (a i) ≠ 0 → (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
      (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i))) ∈
        SP K 𝔭 := by
    intro i hi
    have h1 := hX _ (hGi (Sum.inl i))
    rwa [hg1 i hi, form_smul_left, star_inv_pow hF, map_add, LinearMap.add_apply, hbx, hwx] at h1
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)

  have cf0 : ∀ i, vF 𝔭 (a i) = 0 → f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    rw [hi, pow_zero, mul_one] at hu'
    have e : f (Sum.inl i) = (f (Sum.inl i) * algebraMap F K (a i : F)) *
        (algebraMap F K (a i : F))⁻¹ := by field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf1 : ∀ i, vF 𝔭 (a i) ≠ 0 →
      f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have e : f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) =
        (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf2 : ∀ i, vF 𝔭 (a i) ≠ 0 → f (Sum.inr (τ i)) - f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    obtain ⟨hC0, huc⟩ := UnitPairSolutions.unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    have hua := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have hr := mem_SP_of_inP hu (hcong i hi)
    have hq0 : algebraMap F K (π : F) ^ vF 𝔭 (a i) ≠ 0 := pow_ne_zero _ hϖ0
    have e : f (Sum.inr (τ i)) - f (Sum.inl i) =
        ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
          (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i)))) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) -
        ((algebraMap F K (π : F))⁻¹ ^ (2 * vF 𝔭 (a i)) * algebraMap F K ((a i : F) + c (τ i))) *
          (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      rw [map_add, inv_pow, inv_pow, pow_mul]
      field_simp [hA0 i, hC0, hϖ0]
      ring
    rw [e]
    exact (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem (hσ i hi) huc)
      ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hr (hα i)) hua) huc)
  classical
  set P := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  let z : Fin (finrank K (orthK h U)) → K := fun j =>
    f (Sum.inr j) - ∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)
  have hz : ∀ j, z j ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      have e : ∑ i' ∈ P.filter (fun i' => τ i' = τ i), f (Sum.inl i') = f (Sum.inl i) := by
        apply Finset.sum_eq_single_of_mem
        · simp [hP, hi]
        · intro i' hi' hne
          simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
          exact absurd (hτ i' i hi'.1 hi hi'.2) hne
      show f (Sum.inr (τ i)) - _ ∈ _
      rw [e]; exact cf2 i hi
    · have e : ∑ i' ∈ P.filter (fun i' => τ i' = j), f (Sum.inl i') = 0 := by
        apply Finset.sum_eq_zero
        intro i' hi'
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
        exact absurd ⟨i', hi'.1, hi'.2⟩ hj
      show f (Sum.inr j) - _ ∈ _
      rw [e, sub_zero]
      have h1 := (hunit j (fun i hi e' => hj ⟨i, hi, e'⟩)).2
      rw [map_inv₀] at h1
      have e2 : f (Sum.inr j) = (f (Sum.inr j) * algebraMap F K (c j)) * (algebraMap F K (c j))⁻¹ := by
        field_simp [(map_ne_zero _).2 (hwn j).2]
      rw [e2]; exact (SP K 𝔭).mul_mem (hγ j) h1
  let coef : Fin (finrank K U) → K := fun i => if vF 𝔭 (a i) = 0 then f (Sum.inl i) else
    f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i)
  have hcoef : ∀ i, coef i ∈ SP K 𝔭 := fun i => by
    simp only [coef]; split_ifs with hi
    · exact cf0 i hi
    · exact cf1 i hi
  have hterm : ∀ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) =
      f (Sum.inl i) • b i + (if vF 𝔭 (a i) ≠ 0 then f (Sum.inl i) • w (τ i) else 0) := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · simp only [coef, if_pos hi]
      rw [hg0 i hi, if_neg (fun h' => h' hi), add_zero]
    · simp only [coef, if_neg hi]
      rw [hg1 i hi, if_pos hi, smul_smul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow,
        mul_one, smul_add]
  have hfib : ∑ j, (∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)) • w j =
      ∑ i ∈ P, f (Sum.inl i) • w (τ i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.univ) (g := τ)
      (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hdec : x = ∑ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) + ∑ j, z j • w j := by
    simp only [hterm, Finset.sum_add_distrib, z, sub_smul, Finset.sum_sub_distrib, hfib]
    rw [← Finset.sum_filter]
    conv_lhs => rw [← hf]
    abel
  rw [hdec]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => UnitPairSolutions.smul_mem_locF_of_SP (hcoef i) (hGi _))
    (Submodule.sum_mem _ fun j _ => UnitPairSolutions.smul_mem_locF_of_SP (hz j) (hGw j))

end Formalism.L2.SG.Pf.GluingBases
end
end

section
namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) : GlueExists :=
  glueExists_of_last_dual hL Formalism.L2.SG.Pf.GluingBases.family_dual_holds

end Formalism.L2.SG.Pf.Cnt
end
