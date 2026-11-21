import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

theorem schr_archPair_mem_schA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ _ κ _ ψ hψ h φ hφ
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hφ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ℓ.comp M)
  have hL : ∀ X, L X = ℓ (∑ k, X k * h.2 k) := by
    intro X
    simp [L, M]
  set c : ℝ := ℓ (∑ k, h.1 k * h.2 k) / 2 with hc
  have hgr := GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L (-c) (-1)
  rw [← GlobalTheory.LinPhaseSeminorm.phase_eq] at hgr
  rw [schr_sum']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨SchwartzMap.smulLeftCLM ℂ
      (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((-1 * L x + (-1) ^ 2 * -c : ℝ) : ℂ)))
      (SchwartzMap.compSubConstCLM ℂ (-h.1) (f i)), g i, hg i, ?_⟩
  funext a
  rw [← adeleJoin_archPart F a, schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin,
    GlobalTheory.WeilCont.pureA_adeleJoin, SchwartzMap.smulLeftCLM_apply_apply hgr, SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul, hL, ← mul_assoc]
  congr 2
  rw [hc]
  push_cast
  ring_nf

end GlobalTheory.WeilL2Words

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  atlas_forward_decl GlobalTheory.WeilL2Words.schr_archPair_mem_schA
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace GlobalTheory.WeilL2Convergence

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def rem (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
        (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f) - f - (t : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f -
        (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f)

theorem rem_apply (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) (x : V) :
    rem a L c f t x = Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)) * f (x + t • a) - f x -
      (t : ℂ) * (fderiv ℝ f x a - (2 * Real.pi * Complex.I) * ((L x : ℝ) * f x)) := by
  have htg : Function.HasTemperateGrowth fun x : V => ((L x : ℝ) : ℂ) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  simp only [rem, SchwartzMap.sub_apply, SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.smulLeftCLM_apply_apply htg,
    SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.HeisDer.hasTemperateGrowth_phase L c t),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, sub_neg_eq_add]

theorem seminorm_rem_le (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (rem a L c f t) ≤ C * t ^ 2 := by
  unfold rem
  set P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) with hP
  set d := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hd
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.schwartz_seminorm_smulLeft_linear_phase_le L c k n
  choose C1 hC1 using fun m => GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le a f k m
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le L c d k n
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le L c f k n
  set p := SchwartzMap.seminorm ℂ k n (E := V) (F := ℂ) with hp
  refine ⟨|C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| + |C2| + 2 * Real.pi * p (P d) + |C0|, fun t ht => ?_⟩
  set M : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) with hM
  set X := SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • d with hX
  set Y := M d - d + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P d with hY
  set Z := M f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • P f with hZ
  have e : M (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f) - f - (t : ℂ) • (d - (2 * Real.pi * Complex.I) • P f) =
      M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z := by
    rw [hX, hY, hZ, map_sub, map_sub, map_smul]
    module
  rw [e]
  have t1 : p (M X) ≤ |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by
    refine (hC3 t ht X).trans ?_
    calc C3 * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X
        ≤ |C3| * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m X :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      _ ≤ |C3| * ∑ m ∈ Finset.range (n + 1), |C1 m| * t ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ =>
            (hC1 m t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))) (abs_nonneg _)
      _ = |C3| * (∑ m ∈ Finset.range (n + 1), |C1 m|) * t ^ 2 := by rw [← Finset.sum_mul]; ring
  have t2 : p ((t : ℂ) • Y) ≤ |C2| * t ^ 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := hC2 t ht
    calc |t| * p Y ≤ 1 * (C2 * t ^ 2) := mul_le_mul ht h2 (apply_nonneg _ _) zero_le_one
      _ ≤ |C2| * t ^ 2 := by rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have t3 : p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) = 2 * Real.pi * p (P d) * t ^ 2 := by
    rw [map_smul_eq_mul]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_I,
      abs_of_pos Real.pi_pos, sq_abs]
    ring
  have t4 : p Z ≤ |C0| * t ^ 2 := (hC0 t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have tri : p (M X + (t : ℂ) • Y - ((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d + Z) ≤
      p (M X) + p ((t : ℂ) • Y) + p (((t : ℂ) ^ 2 * (2 * Real.pi * Complex.I)) • P d) + p Z := by
    refine (map_add_le_add p _ _).trans (add_le_add ?_ le_rfl)
    refine (map_sub_le_add p _ _).trans (add_le_add ?_ le_rfl)
    exact map_add_le_add p _ _
  rw [t3] at tri
  nlinarith [t1, t2, t4, tri]

theorem tendsto_rem (a : V) (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) :
    Filter.Tendsto (fun n : ℕ => ((n : ℂ) + 1) • rem a L c f ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, m⟩ ε hε
  obtain ⟨C, hC⟩ := seminorm_rem_le a L c f k m
  have h0 : Filter.Tendsto (fun n : ℕ => C * ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [one_div] using this
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with n hn
  refine lt_of_le_of_lt ?_ hn
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : |((n : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 hp)]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h2 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  rw [sub_zero, SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul, h2]
  refine (mul_le_mul_of_nonneg_left (hC _ h1) hp.le).trans_eq ?_
  field_simp

theorem tendsto_lintegral_sq [MeasurableSpace V] [OpensMeasurableSpace V] [SecondCountableTopology V]
    (μ : Measure V) [μ.HasTemperateGrowth] (u : ℕ → 𝓢(V, ℂ)) (hu : Filter.Tendsto u Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, ‖u n x‖ₑ ^ 2 ∂μ) Filter.atTop (nhds 0) := by
  have h1 := ((SchwartzMap.toLpCLM ℂ ℂ 2 μ).continuous.tendsto 0).comp hu
  rw [map_zero] at h1
  have h2 := (ENNReal.continuous_pow 2).tendsto _ |>.comp (continuous_enorm.tendsto _ |>.comp h1)
  simp only [enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
  rw [Lp.enorm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp (u n) 2 μ)]
  have := eLpNorm_nnreal_pow_eq_lintegral (f := (u n : V → ℂ)) (μ := μ) (p := 2) (by norm_num)
  simpa using this

end Real

theorem tendsto_l2A_diffQuot : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      Filter.Tendsto (fun n : ℕ => GlobalTheory.WeilL2Words.l2A F μ (fun a => ((n : ℂ) + 1) *
        (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) φ a - φ a) - GlobalTheory.WeilL2Words.dS F ψ h φ a))
        Filter.atTop (nhds 0) := by
  intro F _ _ _ κ _ ψ hψ μ hμ h φ hφ
  haveI hO : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth := inferInstance
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨m, f, g, hg, rfl⟩ := GlobalTheory.WeilL2Words.schA_exists_sum F hφ
  have hgc : ∀ i, Continuous (g i) := fun i => (hg i).1.continuous
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hG : ∀ i, ∫⁻ y, ‖g i y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    intro i
    have h := ((hgc i).memLp_of_hasCompactSupport (p := 2) (μ := μ) (hg i).2).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
    simpa using h.ne
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun x => -ℓ (∑ k, x k * h.2 k)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib, add_comm]
      map_smul' := fun r x => by simp [← Finset.smul_sum, Finset.mul_sum] }
  have hL : ∀ x, L x = -ℓ (∑ k, x k * h.2 k) := fun x => rfl
  let c : ℝ := -(ℓ (∑ k, h.1 k * h.2 k) / 2)
  let u : ℕ → Fin m → 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) :=
    fun n i => ((n : ℂ) + 1) • rem h.1 L c (f i) ((n : ℝ) + 1)⁻¹
  have hu : ∀ i, Filter.Tendsto (fun n => ∫⁻ x, ‖u n i x‖ₑ ^ 2) Filter.atTop (nhds 0) :=
    fun i => tendsto_lintegral_sq volume _ (tendsto_rem h.1 L c (f i))
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'
  have e : ∀ n : ℕ, (fun a => ((n : ℂ) + 1) *
        (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a -
          (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) - GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      GlobalTheory.ThetaSobolevBase.sumPure g (u n) := by
    intro n
    funext a
    rw [← GlobalTheory.WeilL2Words.adeleJoin_archPart F a]
    generalize GlobalTheory.WeilL2Words.archPart F a = x
    generalize (fun i => (a i).2) = y
    have e0 : GlobalTheory.ThetaSobolevBase.sumPure g (u n) (GlobalTheory.WeilCont.adeleJoin F x y) = ∑ i, u n i x * g i y := by
      simp only [GlobalTheory.ThetaSobolevBase.sumPure, Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin]
    rw [e0, GlobalTheory.WeilL2Words.schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilL2Words.dS_sum_adeleJoin F ψ ℓ hℓ, hev, hev,
      Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u, SchwartzMap.smul_apply, rem_apply, smul_eq_mul]
    set t : ℝ := ((n : ℝ) + 1)⁻¹ with ht
    have e1 : ∑ k, x k * (t • h).2 k = t • ∑ k, x k * h.2 k := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.smul_snd, Pi.smul_apply]
      exact mul_smul_comm _ _ _
    have e2 : ∑ k, (t • h).1 k * (t • h).2 k = (t ^ 2) • ∑ k, h.1 k * h.2 k := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    have e3 : 2 * Real.pi * Complex.I * ((ℓ (∑ k, x k * (t • h).2 k) : ℂ) + (ℓ (∑ k, (t • h).1 k * (t • h).2 k) : ℂ) / 2) =
        -(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ) := by
      rw [e1, e2, map_smul, map_smul, hL, smul_eq_mul, smul_eq_mul]
      simp only [c]
      push_cast
      ring
    have e4 : ((n : ℂ) + 1) * (t : ℂ) = 1 := by
      rw [ht]
      push_cast
      exact mul_inv_cancel₀ (Nat.cast_add_one_ne_zero n)
    rw [e3, Prod.smul_fst]
    generalize Complex.exp _ = E
    rw [hL]
    push_cast
    linear_combination (fderiv ℝ (f i) x h.1 + 2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x) * g i y * e4
  simp only [e]
  have hlim : Filter.Tendsto (fun n => (m : ENNReal) * ∑ i, (∫⁻ x, ‖u n i x‖ₑ ^ 2) * ∫⁻ y, ‖g i y‖ₑ ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun i _ =>
      ENNReal.Tendsto.mul_const (hu i) (Or.inr (hG i))
    have h2 := ENNReal.Tendsto.const_mul (a := (m : ENNReal)) h1 (Or.inr (ENNReal.natCast_ne_top m))
    simpa using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => GlobalTheory.FoldrBoundLinearForms.l2A_sumPure_le μ g hgc (u n)

end GlobalTheory.WeilL2Convergence

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_haar_weil : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      Filter.Tendsto (fun n : ℕ => GlobalTheory.WeilL2Words.l2A F μ (fun a => ((n : ℂ) + 1) *
        (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) φ a - φ a) - GlobalTheory.WeilL2Words.dS F ψ h φ a))
        Filter.atTop (nhds 0) := by
  atlas_forward_decl GlobalTheory.WeilL2Convergence.tendsto_l2A_diffQuot
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilL2Words

theorem l2A_eq_zero_of_tendsto (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ) (hG : ∀ n, G n ∈ GlobalTheory.WeilM.schA F κ)
    (hD : ∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a)))
    (h0 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0)) : GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := Pi.opensMeasurableSpace
  have hc : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have hin : ∀ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ≤
      liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
    intro y
    have hm : ∀ n, AEMeasurable (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) volume := by
      intro n
      obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hG n) y
      have e : (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) = fun x => ‖s x‖ₑ ^ 2 := by
        funext x; rw [hs]
      rw [e]
      exact (hc.comp s.continuous).measurable.aemeasurable
    calc (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2)
        = ∫⁻ x, liminf (fun n => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
          refine lintegral_congr fun x => ?_
          exact (((hc.tendsto _).comp (hD _)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' hm
  have hmeas : ∀ n, AEMeasurable (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) μ := by
    intro n
    obtain ⟨m, f, g, hg, he⟩ := schA_exists_sum F (hG n)
    have hlc : IsLocallyConstant (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro y
      have hev : ∀ᶠ z in 𝓝 y, ∀ i, g i z = g i y :=
        Filter.eventually_all.2 fun i => (hg i).1.eventually_eq y
      filter_upwards [hev] with z hz
      refine lintegral_congr fun x => ?_
      simp only [he, Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, hz]
    exact hlc.continuous.measurable.aemeasurable
  refine le_antisymm ?_ (bot_le)
  calc l2A F μ D = ∫⁻ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ := rfl
    _ ≤ ∫⁻ y, liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop ∂μ := lintegral_mono hin
    _ ≤ liminf (fun n => ∫⁻ y, (∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ) atTop := lintegral_liminf_le' hmeas
    _ = 0 := h0.liminf_eq

end GlobalTheory.WeilL2Words

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_l2_limit_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ), (∀ n, G n ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a))) →
    Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0) → GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  atlas_forward_decl GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words

theorem eq_zero_of_l2A_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  intro F _ _ κ _ μ hμ D hD h0
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  funext a
  by_contra ha
  set x0 := archPart F a
  set y0 : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2
  have ha0 : D (GlobalTheory.WeilCont.adeleJoin F x0 y0) ≠ 0 := by
    rw [adeleJoin_archPart]; exact ha
  obtain ⟨n, f, g, hg, hDs⟩ := schA_exists_sum F hD
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hD y0
  set V : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i, g i y = g i y0}
  have hVo : IsOpen V := by
    have : V = ⋂ i, {y | g i y = g i y0} := by ext y; simp [V]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hV : ∀ y ∈ V, ∀ x, D (GlobalTheory.WeilCont.adeleJoin F x y) = s x := by
    intro y hy x
    rw [hs, hDs, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.WeilCont.pureA_adeleJoin, GlobalTheory.WeilCont.pureA_adeleJoin, hy i]
  have hsc : Continuous fun x => ‖s x‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp (continuous_enorm.comp s.continuous)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  haveI h1 : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : (∫⁻ x, ‖s x‖ₑ ^ 2) ≠ 0 := by
    intro hc
    have hae := (lintegral_eq_zero_iff' hsc.aemeasurable).1 hc
    have heq := (Continuous.ae_eq_iff_eq volume hsc continuous_const).1 hae
    have : ‖s x0‖ₑ ^ 2 = 0 := congrFun heq x0
    rw [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, hs] at this
    exact ha0 this
  have hμV : μ V ≠ 0 := hVo.measure_ne_zero μ ⟨y0, fun i => rfl⟩
  have hle : (∫⁻ x, ‖s x‖ₑ ^ 2) * μ V ≤ l2A F μ D := by
    rw [← lintegral_indicator_const hVo.measurableSet]
    unfold l2A
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy]
      exact le_of_eq (lintegral_congr fun x => by rw [hV y hy x])
    · rw [Set.indicator_of_notMem hy]; exact bot_le
  rw [h0] at hle
  exact mul_ne_zero hc hμV (le_antisymm hle bot_le)

end GlobalTheory.WeilL2Words
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  atlas_forward_decl GlobalTheory.WeilL2Words.eq_zero_of_l2A_eq_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory

namespace GlobalTheory.WeilL2Words

theorem dS_om_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  intro F _ _ _ κ _ ψ hψ G _ om hpres M himpl μ hμ hiso p h φ hφ
  set h' := M p h with hh'
  have hOm : om p φ ∈ GlobalTheory.WeilM.schA F κ := hpres p φ hφ
  have hD1 : GlobalTheory.WeilL2Words.dS F ψ h' φ ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.WeilL2Words.dS_mem_schA F hψ h' hφ

  set Qr : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n => ((n : ℂ) + 1) •
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h')) φ - φ) - GlobalTheory.WeilL2Words.dS F ψ h' φ with hQr
  have hQr_mem : ∀ n, Qr n ∈ GlobalTheory.WeilM.schA F κ := fun n =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz F κ ψ hψ _ φ hφ) hφ)) hD1
  set Gn : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ := fun n a => ((n : ℂ) + 1) *
      (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) (om p φ) a - om p φ a) -
        om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a with hGn
  have hGQ : ∀ n, Gn n = om p (Qr n) := by
    intro n
    have e := himpl p (((n : ℝ) + 1)⁻¹ • h) φ hφ
    rw [map_smul] at e
    rw [hQr, map_sub, map_smul, map_sub, e]
    funext a
    simp [hGn, smul_eq_mul]
  have hGmem : ∀ n, Gn n ∈ GlobalTheory.WeilM.schA F κ := fun n => by rw [hGQ]; exact hpres p _ (hQr_mem n)
  have hGl2 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) Filter.atTop (nhds 0) := by
    have e : (fun n => GlobalTheory.WeilL2Words.l2A F μ (Gn n)) = fun n => GlobalTheory.WeilL2Words.l2A F μ (Qr n) := by
      funext n; rw [hGQ, hiso p _ (hQr_mem n)]
    rw [e]
    have := GlobalTheory.T.adelic_schwartz_haar_weil F κ ψ hψ μ hμ h' φ hφ
    refine this.congr fun n => ?_
    congr 1
  set D : (κ → AdeleRing (𝓞 F) F) → ℂ := GlobalTheory.WeilL2Words.dS F ψ h (om p φ) - om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) with hD
  have hDmem : D ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (GlobalTheory.WeilL2Words.dS_mem_schA F hψ h hOm) (hpres p _ hD1)
  have hpt : ∀ a, Filter.Tendsto (fun n => Gn n a) Filter.atTop (nhds (D a)) := by
    intro a
    have hd := (GlobalTheory.WeilL2Words.differentiableAt_schr F hψ h hOm a).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div] using h1
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]; positivity
    have h0 : ∀ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h)) Ψ a = Ψ a := by
      intro Ψ
      have : GlobalTheory.WeilL2Words.archPair F ((0 : ℝ) • h) = (0, 0) := by
        rw [zero_smul]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> exact GlobalTheory.WeilL2Words.adeleOfMixedSpaceComponent_zero F
      rw [this]
      simp [GlobalTheory.WeilM.schr]
    have := (hd.comp ht).sub_const (om p (GlobalTheory.WeilL2Words.dS F ψ h' φ) a)
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, h0, hGn, inv_inv, Complex.real_smul]
    push_cast
    ring
  have hl := GlobalTheory.T.adelic_l2_limit_zero F κ μ D Gn hGmem hpt hGl2
  have hz := GlobalTheory.T.adelic_l2_eq_zero_imp_eq_zero F κ μ hμ D hDmem hl
  exact sub_eq_zero.mp hz

end GlobalTheory.WeilL2Words
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_derivative_law_of_L2Isometric : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  atlas_forward_decl GlobalTheory.WeilL2Words.dS_om_eq
end
