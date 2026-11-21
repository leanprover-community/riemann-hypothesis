import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeterssonIntegralHeckeTAdjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSqStatement

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem div_le_half_sq_add {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t / x ≤ (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 := by
  have key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by positivity
  linarith

theorem lseriesSummable_of_sq (a : ℕ → ℂ) (k : ℕ)
    (hsq : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s))
    (s : ℂ) (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable a s := by
  set σ := s.re with hσ
  set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := hsq δ hδ0
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · have : 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := by positivity
    have : 0 ≤ (n : ℝ) ^ (-(1 + δ)) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹ := by
      rw [show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn',
        Real.rpow_neg hn'.le]
    rw [e]
    exact div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)

theorem lseries_cusp_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  intro k L N ε g hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε g hk hL hNL hcf
  have hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n := fun n => by
    have h := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane g hcf.1.1 n
    rw [coef, ← hf] at h
    exact h
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hsq := (GlobalTheory.T.rankin_mean_square_cuspForm k L (ch ε) g hk hcf).2.2.1
  have hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s := lseriesSummable_of_sq g k hsq
  have habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  have hdiff : Differentiable ℂ (ModularForm.L hk0 f) := CuspForm.differentiable_L hk0 f

  have hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s := by
    intro s hs
    have h := CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [LSeries, ← h.tsum_eq]
    congr 1
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hcoef]
  refine ⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩
  set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU
  have hLU : AnalyticOnNhd ℂ (LSeries g) U := (LSeries_analyticOnNhd g).mono fun c hc => by
    simp only [Set.mem_setOf_eq, hU] at hc ⊢
    exact lt_of_le_of_lt habs (by exact_mod_cast hc)
  have hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U := fun z _ => hdiff.analyticAt z
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (k : ℝ) + 2 := by rw [hz₀, Complex.ofReal_re]
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith
  have hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f := by
    have hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc
    exact hagree c hc
  exact hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs

end GlobalTheory.EisM
end
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lseries_extends_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  atlas_forward_decl GlobalTheory.EisM.lseries_cusp_entire
end

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.PetPos

theorem volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  have h0 : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  have hm : Continuous fun z : ℍ => (NNReal.mk z.im z.im_pos.le : NNReal) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :=
    (continuous_const.div₀ hm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).pow 2
  refine ⟨fun U hU hne => ?_⟩
  rw [UpperHalfPlane.volume_def, withDensity_apply _ hU.measurableSet]
  refine ne_of_gt ?_
  have hmeas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.continuous_coe.comp hc).measurable
  rw [setLIntegral_pos_iff hmeas]
  have hsupp : Function.support (fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)) = Set.univ := by
    ext z
    simp [z.im_ne_zero]
    intro h
    have h' := congrArg Subtype.val h
    simp [z.im_ne_zero] at h'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos _ hne

theorem norm_ch_eq_one {L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) (γ : SL(2, ℤ))
    (hγ : (L : ℤ) ∣ γ 1 0) : ‖ch ε (γ 1 1)‖ = 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    rw [hc, mul_zero, sub_zero] at h
    rw [mul_comm]
    exact h
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  show ‖ε ((γ 1 1 : ℤ) : ZMod N)‖ = 1
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one ε u

theorem norm_sq_mul_im_pow_smul {k L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ _
  have hpos : 0 < ‖((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr hD
  rw [hf γ hγ τ, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, norm_mul, norm_mul,
    norm_ch_eq_one ε hNL γ hγ, one_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp
  ring

theorem pet_self_ne_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  intro k L N ε ρ h hk hL hN hW hCF hh
  haveI : (volume : Measure ℍ).IsOpenPosMeasure := volume_isOpenPosMeasure
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hP : PolyB h := hCF.1.1
  have hInv : Inv k L (ch ε) (qs h) := hCF.1.2
  have hqc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hP).2
  set Φ : ℍ → ℝ := fun τ => ‖qs h τ‖ ^ 2 * τ.im ^ k with hΦ
  set G : ℍ → ℝ := fun τ => ρ τ * Φ τ with hG
  have hΦc : Continuous Φ := (hqc.norm.pow 2).mul (UpperHalfPlane.continuous_im.pow k)
  have hGnn : 0 ≤ G := fun τ => mul_nonneg (hW.nonneg τ) (by positivity)
  have heq : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs h τ * (τ.im : ℂ) ^ k)) =
      fun τ => ((G τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.conj_mul']
    simp only [hG, hΦ]
    push_cast
    ring
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (qs h) hk hL hN hW hCF hqc.aestronglyMeasurable
    (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth h hP)
  rw [heq] at hint
  have hGi : Integrable G := by
    have := hint.re
    simpa using this
  intro hzero
  have hpet : pet k ρ (qs h) (qs h) = ((∫ τ, G τ : ℝ) : ℂ) := by
    unfold pet
    rw [heq, integral_complex_ofReal]
  rw [hpet, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg hGnn hGi] at hzero
  have hmp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    intro γ
    have hm := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    convert hm using 1
    ext z
    simp
  have hall : ∀ᵐ τ ∂(volume : Measure ℍ), ∀ γ : Gamma0 L, G ((γ : SL(2, ℤ)) • τ) = 0 := by
    rw [ae_all_iff]
    intro γ
    have h1 := (hmp (γ : SL(2, ℤ))).quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [h1] with τ hτ
    simpa using hτ
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hall] with τ hτ
    have hterm : ∀ γ : Gamma0 L, Φ τ * ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ
      have hγL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
      have hinv := norm_sq_mul_im_pow_smul ε hN hInv (γ : SL(2, ℤ)) hγL τ
      have h2 := hτ γ
      simp only [hG, hΦ] at h2 ⊢
      rw [hinv] at h2
      rw [mul_comm]
      exact h2
    have hs := (hW.sum τ).mul_left (Φ τ)
    simp only [hterm, mul_one] at hs
    exact hs.unique hasSum_zero
  have hΦz : Φ = 0 := (Continuous.ae_eq_iff_eq volume hΦc continuous_const).mp hΦ0
  apply hh
  have hq0 : qs h = qs 0 := by
    funext τ
    have h3 := congrFun hΦz τ
    simp only [hΦ, Pi.zero_apply] at h3
    have him : τ.im ^ k ≠ 0 := pow_ne_zero _ τ.im_ne_zero
    have h4 : ‖qs h τ‖ ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right him
    have h5 : qs h τ = 0 := by simpa using h4
    rw [h5]
    simp [qs]
  exact GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth h 0 hP ⟨0, 0, fun n => by simp⟩ hq0

end GlobalTheory.EisM.PetPos
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  atlas_forward_decl GlobalTheory.EisM.PetPos.pet_self_ne_zero
end

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  atlas_forward_decl GlobalTheory.EisM.finite_smul_mem_fd
end

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma wt_countable : Countable SL(2, ℤ) := by
  have : Function.Injective (fun g : SL(2, ℤ) => fun i j => (g : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro g h e; ext i j; exact congrFun (congrFun e i) j
  exact this.countable

lemma wt_cont (g : SL(2, ℤ)) : Continuous (fun τ : ℍ => g • τ) :=
  continuous_const_smul (g : GL (Fin 2) ℝ)

lemma wt_fd_closed : IsClosed ModularGroup.fd := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const
  exact h1.inter h2

theorem wt_exists : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  haveI := wt_countable
  haveI hfin : Finite (SL(2, ℤ) ⧸ Gamma0 L) := Subgroup.finite_quotient_of_finiteIndex
  set S : Finset SL(2, ℤ) := (Set.finite_range (fun q : SL(2, ℤ) ⧸ Gamma0 L => q.out)).toFinset with hS
  have hcov : ∀ g : SL(2, ℤ), ∃ s ∈ S, ∃ γ ∈ Gamma0 L, g = s * γ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 L) g
    refine ⟨(QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma0 L).out, by simp [hS], ((h⁻¹ : Gamma0 L) : SL(2, ℤ)), (h⁻¹).2, ?_⟩
    rw [hh]; simp
  set K : Set ℍ := {τ | ∃ s ∈ S, s • τ ∈ ModularGroup.fd} with hK
  have hKm : MeasurableSet K := by
    have : K = ⋃ s ∈ S, (fun τ : ℍ => s • τ) ⁻¹' ModularGroup.fd := by
      ext τ; simp [hK]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => (wt_fd_closed.preimage (wt_cont s)).measurableSet
  have hKfin : ∀ τ : ℍ, {γ : Gamma0 L | (γ : SL(2, ℤ)) • τ ∈ K}.Finite := by
    intro τ
    have h1 : {g : SL(2, ℤ) | g • τ ∈ K}.Finite := by
      have : {g : SL(2, ℤ) | g • τ ∈ K} = ⋃ s ∈ S, (fun g => s * g) ⁻¹' {g | g • τ ∈ ModularGroup.fd} := by
        ext g; simp [hK, mul_smul]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet fun s _ =>
        (GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain τ).preimage (mul_right_injective s).injOn
    exact Set.Finite.preimage (f := (Subtype.val : Gamma0 L → SL(2, ℤ))) Subtype.val_injective.injOn h1
  have hKne : ∀ τ : ℍ, ∃ γ : Gamma0 L, (γ : SL(2, ℤ)) • τ ∈ K := by
    intro τ
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hcov g
    exact ⟨⟨γ, hγ⟩, s, hs, by rwa [mul_smul] at hg⟩
  let N : ℍ → ENNReal := fun τ => ∑' γ : Gamma0 L, K.indicator (1 : ℍ → ENNReal) ((γ : SL(2, ℤ)) • τ)
  have hNm : Measurable N := by
    refine Measurable.ennreal_tsum fun γ => ?_
    exact (measurable_one.indicator hKm).comp (wt_cont (γ : SL(2, ℤ))).measurable
  have hNcard : ∀ τ, N τ = ((hKfin τ).toFinset.card : ENNReal) := by
    intro τ
    simp only [N]
    rw [tsum_eq_sum (s := (hKfin τ).toFinset)]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_mem hγ]; simp
    · intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_notMem hγ]
  have hNinv : ∀ (γ : Gamma0 L) τ, N ((γ : SL(2, ℤ)) • τ) = N τ := by
    intro γ τ
    simp only [N]
    rw [← (Equiv.mulRight γ).tsum_eq (fun δ : Gamma0 L => K.indicator (1 : ℍ → ENNReal) ((δ : SL(2, ℤ)) • τ))]
    simp [mul_smul]
  let ρ : ℍ → ℝ := fun τ => K.indicator (fun τ => ((N τ).toReal)⁻¹) τ
  refine ⟨ρ, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (ENNReal.measurable_toReal.comp hNm).inv.indicator hKm
  · intro τ; simp only [ρ]; apply Set.indicator_nonneg; intro τ _; positivity
  · intro τ
    have hz : ∀ γ ∉ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      simp only [ρ]; rw [Set.indicator_of_notMem hγ]
    have hpos : 0 < (hKfin τ).toFinset.card := by
      obtain ⟨γ, hγ⟩ := hKne τ
      exact Finset.card_pos.mpr ⟨γ, by simpa using hγ⟩
    have heq : ∑ γ ∈ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 1 := by
      rw [Finset.sum_congr rfl (g := fun _ => (((hKfin τ).toFinset.card : ℝ))⁻¹)]
      · rw [Finset.sum_const, nsmul_eq_mul]
        have : ((hKfin τ).toFinset.card : ℝ) ≠ 0 := by positivity
        field_simp
      · intro γ hγ
        have hγ' : (γ : SL(2, ℤ)) • τ ∈ K := by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ; exact hγ
        simp only [ρ]
        rw [Set.indicator_of_mem hγ', hNinv, hNcard]
        simp
    exact heq ▸ hasSum_sum_of_ne_finset_zero hz
  · refine ⟨S, fun τ hτ => ?_⟩
    have : τ ∈ K := by
      by_contra h; exact hτ (by simp only [ρ]; rw [Set.indicator_of_notMem h])
    exact this

end GlobalTheory
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gammaZeroPartitionWeight : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  atlas_forward_decl GlobalTheory.wt_exists
end

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
end
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  atlas_forward_decl GlobalTheory.EisMReal.eig_conj
end

section
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZEdge

theorem isUnit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h2 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h2
  rw [ZMod.natCast_self, mul_zero, add_zero] at h2
  exact ⟨⟨(d : ZMod L), (u : ZMod L), by rw [mul_comm]; exact h2, h2⟩, rfl⟩

theorem changeLevel_int {n m : ℕ} (χ : DirichletCharacter ℂ n) (h : n ∣ m) (d : ℤ) (hd : IsUnit (d : ZMod m)) :
    DirichletCharacter.changeLevel h χ (d : ZMod m) = χ (d : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hd.unit
  simp only [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_intCast h]

theorem chi_neg_one (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (hk : Odd k) (hg : Prim k N χ g) :
    χ (-1) = -1 := by
  by_contra hne
  have hinv := hg.cf.1.2 (-1) (by simp)
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have h1 := hinv τ
    have hs : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at h1
    simp [ch, hk.neg_one_pow] at h1
    have h3 : qs g τ * (1 + χ (-1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (by linear_combination h) hne
  have hq0 : qs g = qs 0 := by
    funext τ; rw [hq τ]; simp [qs]
  have hp0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have := GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth g 0 hg.cf.1.1 hp0 hq0
  have h1 := hg.one
  rw [this] at h1
  simp at h1

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem multiplier_agree (N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) :
    ∀ d : ℤ, IsCoprime d ((N * M ^ 2 : ℕ) : ℤ) →
      ch χ d * ch φ d ^ 2 = ch (DirichletCharacter.changeLevel (dvd_mul_right N (M ^ 2)) χ *
        (DirichletCharacter.changeLevel (Dvd.intro_left _ (pow_two M).symm |>.trans (dvd_mul_left _ N)) φ) ^ 2) d := by
  intro d hd
  have hu := isUnit_of_isCoprime hd
  simp only [ch, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  rw [changeLevel_int χ _ d hu, changeLevel_int φ _ d hu]

theorem exists_entire (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hk : 1 ≤ k) (hN : 0 < N) (hM : 0 < M) (hg : CF k N (ch χ) g) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re →
      LSeries (fun n => φ n * g n) s = Λ s := by
  have ht := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k N M χ φ g hM hg
  have hmf := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * M ^ 2) _).2.2.2.1 _ _ (multiplier_agree N M χ φ) ht.1
  obtain ⟨Λ, h1, h2⟩ := GlobalTheory.T.cuspForm_lseries_extends_entire k (N * M ^ 2) (N * M ^ 2) _ _ hk (by positivity) dvd_rfl ⟨hmf, ht.2⟩
  exact ⟨Λ, h1, fun s hs => (h2 s hs).2⟩

theorem norm_b_sq (e n : ℕ) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow, ← pow_mul, mul_comm e 2, mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one φ _))

theorem term_le (e n : ℕ) (s : ℝ) (hs : 0 < s) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show ((0 : ℕ) : ℝ) = 0 from Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by positivity), div_zero, div_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc _ ≤ (‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e)) / (n : ℝ) ^ (1 + s) :=
          div_le_div_of_nonneg_right (norm_b_sq e n φ g) (by positivity)
      _ = _ := by
          rw [div_div]; congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_add hn']; congr 1; push_cast; ring

theorem lseries_shift (e : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    LSeries (fun n => a n / (n : ℂ) ^ e) z = LSeries a (z + e) := by
  unfold LSeries; congr 1; funext n
  simp only [LSeries.term]
  split_ifs with h
  · rfl
  · rw [cpow_add _ _ (Nat.cast_ne_zero.2 h), cpow_natCast, div_div, mul_comm]

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem b_props (e N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hN : 0 < N) (hg : Prim (2 * e + 1) N χ g) (hχ : χ (-1) = -1) (hg0 : g 0 = 0) :
    let b : ℕ → ℂ := fun n => φ n * g n / (n : ℂ) ^ e
    let ω : ℕ → ℂ := fun p => χ p * φ p ^ 2
    b 1 = 1 ∧ b 0 = 0 ∧ (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) ∧
    (∀ n, ¬ n.Coprime (N * M) → b n = 0) ∧
    (∀ p r : ℕ, p.Prime → ¬ p ∣ N * M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * M → (p : ZMod (N * M)) = -1 → (b p).re = 0) := by
  intro b ω
  obtain ⟨hmul, hrec, -⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg
  refine ⟨by simp [b, hg.one], by simp [b, hg0], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    simp only [b, Nat.cast_mul, map_mul, hmul m n hmn, mul_pow]
    ring
  · intro n hn
    simp only [b]
    by_cases hnN : n.Coprime N
    · have hnM : ¬ n.Coprime M := fun h => hn (Nat.Coprime.mul_right hnN h)
      rw [MulChar.map_nonunit φ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul, zero_div]
    · rw [hg.zero n hnN, mul_zero, zero_div]
  · intro p r hp hpd
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have huN : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine ⟨?_, ?_⟩
    · simp only [ω, norm_mul, norm_pow]
      have h1 := DirichletCharacter.unit_norm_eq_one χ huN.unit
      simp only [IsUnit.unit_spec] at h1
      rw [h1, one_mul]
      have hpM : ¬ p ∣ M := fun h => hpd (dvd_mul_of_dvd_right h N)
      have huM : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have h2 := DirichletCharacter.unit_norm_eq_one φ huM.unit
      simp only [IsUnit.unit_spec] at h2
      rw [h2, one_pow]
    · simp only [b, Nat.cast_pow, map_pow, hrec p r hp hpN, ω]
      rw [show 2 * e + 1 - 1 = 2 * e by omega]
      field_simp
      ring
  · intro p hp hpd hpm
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have hcN : (p : ZMod N) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N M) (ZMod N)) hpm
      simpa using this
    have hcM : (p : ZMod M) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_left M N) (ZMod M)) hpm
      simpa using this
    have hreal := GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj (2 * e + 1) N p χ g (by omega) hN hg hp hpN
    simp only [ch, Int.cast_natCast, hcN, hχ] at hreal
    have hre : (g p).re = 0 := by
      have := congrArg Complex.re hreal
      simp at this
      linarith
    have hφ : φ (-1) = 1 ∨ φ (-1) = -1 := by
      have h2 : φ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
      have h3 : (φ (-1) - 1) * (φ (-1) + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · left; linear_combination h
      · right; linear_combination h
    simp only [b, hcM]
    rw [← Nat.cast_pow, Complex.div_natCast_re]
    rcases hφ with h | h <;> simp [h, hre]

end GlobalTheory.EisM.ZEdge

theorem GlobalTheory.EisM.twisted_lvalue_ne_zero_edge : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  intro k N M χ φ g w hk hN hM hg hw
  have hχ := GlobalTheory.EisM.ZEdge.chi_neg_one k N χ g hk hg
  refine ⟨hχ, ?_⟩
  obtain ⟨e, rfl⟩ := hk
  obtain ⟨Λ, hΛd, hΛ⟩ := GlobalTheory.EisM.ZEdge.exists_entire (2 * e + 1) N M χ φ g (by omega) hN hM hg.cf
  obtain ⟨hg0, ⟨C1, hC1⟩, hsum, ⟨C2, hC2⟩⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hg.cf
  obtain ⟨hb1, hb0, hbm, hbz, hbr, hbre⟩ := GlobalTheory.EisM.ZEdge.b_props e N M χ φ g hN hg hχ hg0
  have hkw : (e : ℝ) + 1 ≤ w := by push_cast at hw; linarith
  have hne : Λ w ≠ 0 := by
    have key := GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity (N * M) (fun n => φ n * g n / (n : ℂ) ^ e) (fun p => χ p * φ p ^ 2) (max C1 C2)
      (fun z => Λ (z + e)) (by positivity) hb1 hb0 hbm hbz hbr ?_ ?_ ?_ hbre ?_ ?_ (w - e) (by linarith)
    · have hc : (((w - e : ℝ)) : ℂ) + (e : ℂ) = (w : ℂ) := by push_cast; ring
      simpa [hc] using key
    · intro n
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [hg0]
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        calc ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := GlobalTheory.EisM.ZEdge.norm_b_sq e n φ g
          _ ≤ C1 * (n : ℝ) ^ (2 * e + 1) / (n : ℝ) ^ (2 * e) := div_le_div_of_nonneg_right (hC1 n) (by positivity)
          _ = C1 * n := by field_simp; ring
          _ ≤ max C1 C2 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le
    · intro s hs
      exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)
    · intro s hs hs1
      calc s * ∑' n : ℕ, ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s)
          ≤ s * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
            apply mul_le_mul_of_nonneg_left _ hs.le
            exact Summable.tsum_le_tsum (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g)
              (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)) (hsum s hs)
        _ ≤ C2 := hC2 s hs hs1
        _ ≤ max C1 C2 := le_max_right _ _
    · exact hΛd.comp (differentiable_id.add_const _)
    · intro s hs
      show LSeries (fun n => φ n * g n / (n : ℂ) ^ e) _ = Λ (_ + e)
      rw [GlobalTheory.EisM.ZEdge.lseries_shift e (fun n => φ n * g n)]
      apply hΛ
      simp
      push_cast
      linarith
  refine ⟨Λ w, hne, ?_⟩
  have hc : Tendsto (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (Λ w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) :=
      hΛd.continuous.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
    simpa using this.tendsto 0
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hΛ]
  simp
  push_cast
  have : (0 : ℝ) < s := hs
  linarith
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  atlas_forward_decl GlobalTheory.EisM.twisted_lvalue_ne_zero_edge
end
