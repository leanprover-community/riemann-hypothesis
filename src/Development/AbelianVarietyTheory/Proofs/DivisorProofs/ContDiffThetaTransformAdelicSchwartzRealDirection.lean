import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz

section
section
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  choose u hus hub using hu
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl
  rw [hinf] at hf ⊢
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro t₀
  let ρ : ContDiffBump t₀ := ⟨1/2, 1, by norm_num, by norm_num⟩
  set R : ℝ := ‖t₀‖ + 1 with hR
  let ρc : (Fin k → ℝ) → ℂ := fun t => ((ρ t : ℝ) : ℂ)
  have hρc : ContDiff ℝ ∞ ρc := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have hρcs : HasCompactSupport ρc := ρ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B := fun j =>
    (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hρcs.iteratedFDeriv j)
  choose B hB using hB
  have hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0 := by
    intro j x hx
    by_contra h
    have hx1 : x ∈ tsupport ρc := support_iteratedFDeriv_subset j h
    have h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ) :=
      tsupport_comp_subset Complex.ofReal_zero _
    rw [ρ.tsupport_eq] at h2
    exact hx (h2 hx1)
  have hunonneg : ∀ m i, 0 ≤ u m R i := fun m i =>
    (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  let v : ℕ → ι → ℝ := fun m i =>
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i
  have hv : ∀ m, Summable (v m) := fun m => by
    apply summable_sum
    intro j _
    exact (hus (m - j) R).mul_left _
  have hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i := by
    intro m i x
    refine (norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : x ∈ Metric.closedBall t₀ 1
    · have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have := norm_sub_norm_le x t₀
        rw [hR]; linarith
      apply mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _)
        (mul_nonneg (by positivity) (hB0 j))
      exact mul_le_mul_of_nonneg_left (hB j x) (by positivity)
    · rw [hsupp j x hx, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)
  have hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t) :=
    contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top))
      (fun m _ => hv m) (fun m i x _ => hbound m i x)
  have heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t) := by
    filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [tsum_mul_left]
    have h1 : ρ t = 1 := ρ.one_of_mem_closedBall ht
    simp [ρc, h1]
  exact (hsm.contDiffAt).congr_of_eventuallyEq heq

end GlobalTheory
end

open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  atlas_forward_decl GlobalTheory.contDiff_tsum_of_locally_summable_bounds
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.PsiInfLinear

theorem continuous_ringEquiv_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem psiInf_eq_exp_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F,
      psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  intro D ψ h
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
    refine continuous_const.mul (continuous_finset_sum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (continuous_ringEquiv_mixedSpace_symm D.host.F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [e.symm_apply_apply]

end GlobalTheory.PsiInfLinear
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F, psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  first | exact @GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | exact GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | (intros; apply GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear <;> assumption)
end

section
section
open scoped ContDiff
open scoped Nat

noncomputable section

namespace GlobalTheory

theorem norm_iteratedFDeriv_real_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

theorem norm_iteratedFDeriv_succ_clm_add_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ∞ h) (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ (i + 1) (fun t => L t + h t) t‖ ≤ ‖L‖ + ‖iteratedFDeriv ℝ (i + 1) h t‖ := by
  have hd : ∀ s, DifferentiableAt ℝ h s := fun s =>
    (hh.differentiable (by simp)).differentiableAt
  have hf : fderiv ℝ (fun t => L t + h t) = fun s => L + fderiv ℝ h s := by
    funext s
    exact (L.hasFDerivAt.add (hd s).hasFDerivAt).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, ← norm_iteratedFDeriv_fderiv]
  have hfh : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ i ((fun _ => L) + fderiv ℝ h) t‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_const (c := L)).contDiffAt (hfh.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simp

theorem norm_iteratedFDeriv_cexp_phase_le :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring

end GlobalTheory
end
end

open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_cexp_phase_le' : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  atlas_forward_decl GlobalTheory.norm_iteratedFDeriv_cexp_phase_le
end

section
section
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_shift_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  set S : ℝ := 2 ^ M * (Finset.Iic (M, n)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hS
  set B : ℝ := ‖a‖ + ‖p‖ * max R 0 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨‖p‖ ^ n * ((1 + B) ^ M * S), fun y t ht => ?_⟩
  have hy0 : 0 < (1 + ‖y‖) ^ M := by positivity

  have hcomp : (fun t => f (y + a + p t)) = (fun v => f (y + a + v)) ∘ p := rfl
  have hg : ContDiff ℝ ∞ (fun v => f (y + a + v)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  have e1 := ContinuousLinearMap.iteratedFDeriv_comp_right p hg t (i := n)
    (by exact_mod_cast le_top)
  have e2 : iteratedFDeriv ℝ n (fun v => f (y + a + v)) (p t)
      = iteratedFDeriv ℝ n f (y + a + p t) := iteratedFDeriv_comp_add_left n (y + a) (p t)
  set v := y + a + p t with hv
  have hD : ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := by
    rw [hcomp, e1, e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const, mul_comm]

  have hdec : (1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M, n)) le_rfl le_rfl f v

  have hpt : ‖p t‖ ≤ ‖p‖ * max R 0 :=
    (p.le_opNorm t).trans (mul_le_mul_of_nonneg_left (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have hyv : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + B) := by
    have : y = v - a - p t := by rw [hv]; abel
    have h1 : ‖y‖ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by
      rw [this]
      calc ‖v - a - p t‖ ≤ ‖v - a‖ + ‖p t‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + ‖a‖ + ‖p t‖ := by gcongr; exact norm_sub_le _ _
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith [mul_nonneg hv0 hB0]
  have hyM : (1 + ‖y‖) ^ M ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hyv M
  have hDf0 : 0 ≤ ‖iteratedFDeriv ℝ n f v‖ := norm_nonneg _
  have key : (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S := by
    calc (1 + ‖y‖) ^ M * ‖iteratedFDeriv ℝ n f v‖
        ≤ (1 + ‖v‖) ^ M * (1 + B) ^ M * ‖iteratedFDeriv ℝ n f v‖ :=
          mul_le_mul_of_nonneg_right hyM hDf0
      _ = (1 + B) ^ M * ((1 + ‖v‖) ^ M * ‖iteratedFDeriv ℝ n f v‖) := by ring
      _ ≤ (1 + B) ^ M * S := mul_le_mul_of_nonneg_left hdec (by positivity)
  have hf' : ‖iteratedFDeriv ℝ n f v‖ ≤ (1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_comm]; exact key
  calc ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖
      ≤ ‖p‖ ^ n * ‖iteratedFDeriv ℝ n f v‖ := hD
    _ ≤ ‖p‖ ^ n * ((1 + B) ^ M * S * ((1 + ‖y‖) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left hf' (by positivity)
    _ = ‖p‖ ^ n * ((1 + B) ^ M * S) * ((1 + ‖y‖) ^ M)⁻¹ := by ring

end GlobalTheory
end

open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap V ℂ) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  atlas_forward_decl GlobalTheory.schwartz_shift_iteratedFDeriv_bound
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LatSumSB

open GlobalTheory.WeilM GlobalTheory.ThetaTrCont

theorem summable_sb_mul_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ *
        ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  intro F _ _ κ _ g hg a
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hK : IsCompact ((fun z => z - a) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, fun c => ?_⟩
  set M := Module.finrank ℤ (denomLattice F κ N) + 1
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_left ?_ _
    rw [norm_eq_zero]
    by_contra h0
    apply hξ
    have hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ (fun z => z - a) '' tsupport g :=
      ⟨_, subset_tsupport _ h0, by funext i; simp⟩
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy'⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hKN _ hy i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy'
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded
      ((((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
        ((1 + ‖c‖) ^ M)).mul_left B) fun ξ => ?_
    set z : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ.1 i)
    have hz : ‖(j ξ : denomLattice F κ N)‖ = ‖z‖ := rfl
    simp only [Function.comp_apply, hz]
    have hpos1 : 0 < (1 + ‖z + c‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hpos2 : 0 < (1 + ‖z‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hw : ((1 + ‖z + c‖) ^ M)⁻¹ ≤ (1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos2, ← div_eq_inv_mul, div_le_iff₀ hpos1, ← mul_pow, mul_comm (1 + ‖c‖)]
      exact pow_le_pow_left₀ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).le (one_add_norm_le z c) M
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos1.le)]
    calc ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i) + a i)‖ * ((1 + ‖z + c‖) ^ M)⁻¹
        ≤ B * ((1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹) :=
          mul_le_mul (hB _) hw (inv_nonneg.2 hpos1.le) ((norm_nonneg _).trans (hB 0))
      _ = _ := rfl

end GlobalTheory.LatSumSB
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F, Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ * ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  atlas_forward_decl GlobalTheory.LatSumSB.summable_sb_mul_decay
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.RealDirCoord

theorem continuous_ringEquiv_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem eps_smul_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (z : AF F ⊗[F] E) :
    (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)
    simp
  | add a b ha hb => rw [smul_add, ha, hb, map_add, map_add]; rfl

theorem eps_smul_eq (D : D7) (z : AE D) :
    (pairA D.host.F 0 1) • z =
      LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (finPart D z) :=
  eps_smul_gen z

theorem eps_mul_snd {F : Type} [Field F] [NumberField F] (x : AF F) :
    (pairA F 0 1 * x).2 = x.2 := one_mul x.2

theorem darboux_real_coords : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  intro D S T κ _ e k L hL hfin

  have hε : ∀ t, (pairA D.host.F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPart D (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]
    rfl
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩

  have he : Continuous e := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
      inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
        map_add' := by
          intro a b
          funext i
          rw [map_add, LinearEquiv.map_add, hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (continuous_ringEquiv_mixed D.host.F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

end GlobalTheory.RealDirCoord
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_real_family_archimedean_linear : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  first | exact @GlobalTheory.RealDirCoord.darboux_real_coords | exact GlobalTheory.RealDirCoord.darboux_real_coords | (intros; apply GlobalTheory.RealDirCoord.darboux_real_coords <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical ContDiff

noncomputable section

namespace GlobalTheory.ThetaSmooth

theorem norm_iteratedFDeriv_exp_mul_schwartz_le {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap V ℂ) (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ) (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hre : ∀ y t, (B y t + h t).re = 0) (a : V) (p : E →L[ℝ] V) (n M : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t) * f (y + a + p t)) t‖ ≤ C * ((1 + ‖y‖) ^ M)⁻¹ := by
  choose C1 hC1 using fun j => GlobalTheory.T.norm_iteratedFDeriv_cexp_phase_le' B h hh hre j R
  choose C2 hC2 using fun j => GlobalTheory.T.schwartz_iteratedFDeriv_shift_le_inv_pow_of_norm_le f a p j (M + n) R
  refine ⟨∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |C1 j| * |C2 (n - j)|, fun y t ht => ?_⟩
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have s1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => Complex.exp (B y t + h t) :=
    Complex.contDiff_exp.comp ((B y).contDiff.add hh)
  have s2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => f (y + a + p t) :=
    (f.smooth ⊤).comp (contDiff_const.add p.contDiff)
  refine (norm_iteratedFDeriv_mul_le s1 s2 t (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e1 := hC1 j y t ht
  have e2 := hC2 (n - j) y t ht
  have hpow : (1 + ‖y‖) ^ j * ((1 + ‖y‖) ^ (M + n))⁻¹ ≤ ((1 + ‖y‖) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), pow_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ hy1 hjn
  calc (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun t => Complex.exp (B y t + h t)) t‖ *
        ‖iteratedFDeriv ℝ (n - j) (fun t => f (y + a + p t)) t‖
      ≤ (n.choose j : ℝ) * (|C1 j| * (1 + ‖y‖) ^ j) * (|C2 (n - j)| * ((1 + ‖y‖) ^ (M + n))⁻¹) := by
        gcongr
        · exact e1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        · exact e2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ = (n.choose j : ℝ) * |C1 j| * |C2 (n - j)| * ((1 + ‖y‖) ^ j * ((1 + ‖y‖) ^ (M + n))⁻¹) := by ring
    _ ≤ (n.choose j : ℝ) * |C1 j| * |C2 (n - j)| * ((1 + ‖y‖) ^ M)⁻¹ := by gcongr

set_option maxHeartbeats 2000000 in

theorem contDiff_thetaTr_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L →
          (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) := by
  intro D ψ hψ S T JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  obtain ⟨P, Q, hPQ⟩ := GlobalTheory.T.darbouxCoords_real_family_archimedean_linear D S T κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear D ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1

  suffices key : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ w,
      Summable (fun x : κ → D.host.F => co.rho ψ w Φ (fun i => algebraMap D.host.F (AF D.host.F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF D.host.F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF D.host.F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF D.host.F) → ℂ) = 0 := by
    intro w; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M, hM⟩ := GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay D.host.F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    let yv : (κ → D.host.F) → (κ → mixedEmbedding.mixedSpace D.host.F) := fun x i => mixedEmbedding D.host.F (x i)
    let ah : κ → mixedEmbedding.mixedSpace D.host.F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace D.host.F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace D.host.F := eM (⅟(2 : AF D.host.F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace D.host.F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace D.host.F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)
    have hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i) := fun y t => rfl
    let hfun : (Fin k → ℝ) → ℂ := fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))
    have hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i :=
      fun i => ((ContinuousLinearMap.proj i).comp P).contDiff
    have hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i :=
      fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
      Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
        ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))
    have hre : ∀ y t, (B y t + hfun t).re = 0 := by
      intro y t; rw [hB, ← map_add]; exact hΛre _
    let K : (κ → D.host.F) → ℂ := fun x =>
      ψ ((fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) *
        g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2)
    let G : (κ → D.host.F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → D.host.F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t

    have hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA D.host.F f g)
        (fun i => algebraMap D.host.F (AF D.host.F) (x i)) = term x t := by
      intro x t
      have he : co.e (w + L t) = ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0,
          (co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) := by
        rw [map_add, hPQ t]; rfl
      have hy : ∀ i, eM (algebraMap D.host.F (AF D.host.F) (x i)).1 = yv x i := by
        intro i; simp only [yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
          (((fun i => algebraMap D.host.F (AF D.host.F) (x i)) +
            ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t := by
        funext i
        change eM ((algebraMap D.host.F (AF D.host.F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add, map_add, RingEquiv.apply_symm_apply, hy i, ← add_assoc]
        rfl
      have h2 : (fun i => (((fun i => algebraMap D.host.F (AF D.host.F) (x i)) +
            ((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0)) i).2) =
          fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2 := by
        funext i
        change (algebraMap D.host.F (AF D.host.F) (x i)).2 + (((co.e w).1 i).2 + 0) = _
        rw [add_zero]
        rfl
      have hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA D.host.F f g) (fun i => algebraMap D.host.F (AF D.host.F) (x i)) =
          ψ ((fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
            ⅟2 * (((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ
              ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0))) *
          (f (yv x + ah + P t) * g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
            ((co.e w).1 i).2)) := by
        rw [← h1, ← h2]
        show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _
        rw [he]
        rfl
      rw [hL]
      let φ : AF D.host.F →+* mixedEmbedding.mixedSpace D.host.F := eM.toRingHom.comp (fstA D.host.F).toRingHom
      let φf : AF D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F := (sndA D.host.F).toRingHom
      have hφx : ∀ i, φ (algebraMap D.host.F (AF D.host.F) (x i)) = yv x i := hy
      have hφP : ∀ i, φ (pairA D.host.F (eM.symm (P t i)) 0) = P t i := fun i => eM.apply_symm_apply _
      have hφQ : ∀ i, φ (pairA D.host.F (eM.symm (Q t i)) 0) = Q t i := fun i => eM.apply_symm_apply _
      have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun i => rfl
      have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun i => rfl
      have hφ2 : φ ⅟2 = c2 := rfl
      have hφdef : ∀ z : AF D.host.F, eM z.1 = φ z := fun _ => rfl
      have hφfdef : ∀ z : AF D.host.F, z.2 = φf z := fun _ => rfl
      have hφpair : ∀ n, φ (pairA D.host.F (eM.symm n) 0) = n := fun n => eM.apply_symm_apply _
      have hφfpair : ∀ n, φf (pairA D.host.F (eM.symm n) 0) = 0 := fun n => rfl
      have hφfP : ∀ i, φf (pairA D.host.F (eM.symm (P t i)) 0) = 0 := fun i => rfl
      have hφfQ : ∀ i, φf (pairA D.host.F (eM.symm (Q t i)) 0) = 0 := fun i => rfl
      set X := (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)
        with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ
            ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
          ⅟2 * (((co.e w).1 + fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ
            ((co.e w).2 + fun i => pairA D.host.F (eM.symm (Q t i)) 0)) = X + pairA D.host.F (eM.symm m) 0 := by
        have hY : (fun i => algebraMap D.host.F (AF D.host.F) (x i)) ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
            ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0) +
              (fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 +
              (fun i => pairA D.host.F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA D.host.F (eM.symm (Q t i)) 0)) =
            pairA D.host.F (eM.symm m) 0 := by
          refine Prod.ext ?_ ?_
          · apply eM.injective
            rw [hφdef, hφdef, hφpair, hm]
            simp only [dotProduct, map_add, map_mul, map_sum, hφx, hφP, hφQ, hφa, hφb, hφ2, Finset.sum_add_distrib]
          · rw [hφfdef, hφfdef, hφfpair]
            simp only [dotProduct, map_add, map_mul, map_sum, hφfP, hφfQ, mul_zero, zero_mul, Finset.sum_const_zero,
              add_zero]
        rw [← hY, hX]
        simp only [dotProduct_add, add_dotProduct]
        ring
      have hψY : ψ (pairA D.host.F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf D.host.F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F = eM from rfl, RingEquiv.apply_symm_apply, hm,
          map_add]
        rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]
      simp only [term, K, G]
      ring
    have hK : ∀ x, ‖K x‖ =
        ‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) + ((co.e w).1 i).2)‖ := by
      intro x; simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → D.host.F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
        ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      have h1 := hC (yv x) t ht
      calc _ ≤ ‖g (fun i => algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i) +
            ((co.e w).1 i).2)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.WeilM.pureA D.host.F f g) (w + L t)) =
          fun t => ∑' x, term x t := funext fun t => tsum_congr fun x => hid x t
      rw [e]
      exact GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds term hsmooth hbd
  | zero =>
    intro w
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, rho_zero, Pi.zero_apply]
    exact ⟨summable_zero, by simpa [GlobalTheory.WeilM.thetaSum] using contDiff_const⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    intro w
    refine ⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₁ (w + L t) +
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2

end GlobalTheory.ThetaSmooth

end
end
