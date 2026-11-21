import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSec

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

def TK (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ InG M}

theorem isCompact_TK : IsCompact (TK n) := by
  have hsub : TK n ⊆ Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro M hM i _ j _
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hM.1
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hc1 : IsClosed {M : M2 n | Mᴴ * M = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hc2 : IsClosed {M : M2 n | Mᴴ * JJ n * M = JJ n} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact hc1.inter hc2

def toGR (M : TK n) : GR n :=
  ⟨⟨M.1, M.1ᴴ, mul_eq_one_comm.mp M.2.1, M.2.1⟩, M.2.2⟩

theorem continuous_toGR : Continuous (toGR (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem isCompact_KR : IsCompact ((KR n : Set (GR n))) := by
  have hset : (KR n : Set (GR n)) = Set.range (toGR (n := n)) := by
    ext k
    constructor
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨M, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
  haveI : CompactSpace (TK n) := isCompact_iff_compactSpace.mp isCompact_TK
  rw [hset]
  exact isCompact_range continuous_toGR

instance compactSpace_KR : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

end PositivityTheory.Rg.Sw.AbsSt.SD
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

theorem herm_smul {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : ((σ : ℂ) • H).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH.eq]
  simp

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hb.eq]

def nGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := nU ((σ : ℂ) • H)
  inv := nU (-((σ : ℂ) • H))
  val_inv := by rw [nU_mul_nU, add_neg_cancel, nU_zero]
  inv_val := by rw [nU_mul_nU, neg_add_cancel, nU_zero]

def nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨nGU H σ, inG_nU (herm_smul hH σ)⟩

theorem mR_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : mR (nG hH σ) = nU ((σ : ℂ) • H) := rfl

theorem cont_nG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (nG hH) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) ((σ : ℂ) • H) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const)
      continuous_const continuous_const
  · show Continuous fun σ : ℝ => fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-((σ : ℂ) • H)) 0 1
    exact Continuous.matrix_fromBlocks continuous_const ((Complex.continuous_ofReal).smul continuous_const).neg
      continuous_const continuous_const

theorem nG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : nG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_nG, DF.mR_one]
  simp [DF.nU_zero]

def eH (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

theorem eH_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [eH, neg_smul]

theorem eH_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H σ * eH H (-σ) = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_right, add_neg_cancel]
  simp

theorem eH_neg_mul (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : eH H (-σ) * eH H σ = 1 := by
  rw [eH_neg]
  unfold eH
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((σ : ℂ) • H)).neg_left, neg_add_cancel]
  simp

theorem eH_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (eH H σ)ᴴ = eH H σ := by
  rw [eH, ← Matrix.exp_conjTranspose, (herm_smul hH σ).eq]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem cont_eH (H : Matrix (Fin n) (Fin n) ℂ) : Continuous (eH H) :=
  NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal).smul continuous_const)

def mGU (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks (eH H σ) 0 0 (eH H (-σ))
  inv := fromBlocks (eH H (-σ)) 0 0 (eH H σ)
  val_inv := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]
  inv_val := by rw [fromBlocks_multiply]; simp [eH_mul_neg, eH_neg_mul, fromBlocks_one]

theorem inG_mGU {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    InG (fromBlocks (eH H σ) 0 0 (eH H (-σ))) := by
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [eH_herm hH, eH_mul_neg, eH_neg_mul]

def mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : GR n := ⟨mGU H σ, inG_mGU hH σ⟩

theorem mR_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) :
    mR (mG hH σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) := by
  rw [← eH_neg]
  rfl

theorem cont_mG {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Continuous (mG hH) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have h1 := cont_eH H
  have h2 : Continuous fun σ : ℝ => eH H (-σ) := h1.comp continuous_neg
  constructor
  · exact Continuous.matrix_fromBlocks h1 continuous_const continuous_const h2
  · exact Continuous.matrix_fromBlocks h2 continuous_const continuous_const h1

theorem mG_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : mG hH 0 = 1 := by
  apply DF.ext_mR
  rw [mR_mG, DF.mR_one]
  simp [Matrix.fromBlocks_one]

theorem unif_family (S D : GR n → ℂ) (hS : Continuous S) (hD : Continuous D) (f : ℝ → GR n) (hf : Continuous f)
    (hf0 : f 0 = 1)
    (hd : ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∀ s : ℝ, HasDerivAt (fun σ : ℝ => S (g * f σ)) (D (g * f s)) s)
    (y : GR n) : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(S ((k : GR n) * y * f s) - S ((k : GR n) * y)) / s - D ((k : GR n) * y)‖ ≤ δ := by
  intro δ hδ
  have hcontD : Continuous fun p : GR n × ℝ => D (p.1 * f p.2) :=
    hD.comp (continuous_fst.mul (hf.comp continuous_snd))
  have ftc : ∀ s : ℝ, ∀ g : GR n, S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ) := by
    intro s
    have hcl : IsClosed {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      apply isClosed_eq
      · exact (hS.comp (continuous_id.mul continuous_const)).sub hS
      · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun g σ => D (g * f σ)) hcontD 0 s
    have hsub : {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ⊆
        {g : GR n | S (g * f s) - S g = ∫ σ in (0:ℝ)..s, D (g * f σ)} := by
      intro g hg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun σ => S (g * f σ)) (f' := fun σ => D (g * f σ)) (fun x _ => hd g hg x)
        ((hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s)
      simp only [hf0, mul_one] at h
      exact h.symm
    intro g
    have h := hcl.closure_subset_iff.mpr hsub
    rw [DF.dense_cell.closure_eq] at h
    exact h (Set.mem_univ g)
  have htube : ∀ᶠ σ in 𝓝 (0:ℝ), ∀ k ∈ (Set.univ : Set (KR n)),
      ‖D ((k : GR n) * y * f σ) - D ((k : GR n) * y)‖ < δ := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro k _
    have hc : Continuous fun p : ℝ × KR n => ‖D ((p.2 : GR n) * y * f p.1) - D ((p.2 : GR n) * y)‖ :=
      ((hD.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul
        (hf.comp continuous_fst))).sub
        (hD.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).norm
    have h0 : ‖D ((k : GR n) * y * f 0) - D ((k : GR n) * y)‖ < δ := by simp [hf0, hδ]
    exact Filter.eventually_of_mem ((hc.isOpen_preimage _ isOpen_Iio).mem_nhds h0) (fun z hz => hz)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp htube
  refine ⟨η, hη, fun s hs hsη k => ?_⟩
  set g := (k : GR n) * y with hg
  rw [ftc s g]
  have hint : IntervalIntegrable (fun σ => D (g * f σ)) MeasureTheory.volume 0 s :=
    (hD.comp (continuous_const.mul hf)).intervalIntegrable 0 s
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : (∫ σ in (0:ℝ)..s, D (g * f σ)) / s - D g = (∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)) / s := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, sub_div, mul_div_cancel_left₀ _ hs']
  have hb : ‖∫ σ in (0:ℝ)..s, (D (g * f σ) - D g)‖ ≤ δ * |s - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : |x| ≤ |s| := by
      rcases Set.mem_uIoc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le_abs h2 (by linarith)
      · rw [abs_of_nonpos h2, abs_of_neg (by linarith)]
        linarith
    have hx2 : dist x 0 < η := by
      rw [dist_zero_right, Real.norm_eq_abs]
      linarith
    exact (hball hx2 k (Set.mem_univ _)).le
  have hs0 : (0:ℝ) < ‖(s:ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_pos.mpr hs
  rw [key, norm_div, div_le_iff₀ hs0]
  calc _ ≤ δ * |s - 0| := hb
    _ = δ * ‖(s:ℂ)‖ := by rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]

end PositivityTheory.Rg.Sw.AbsSt.SD

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SD

theorem secDer_of (hN : NDer) (hM : MDer) : SecDer := by
  intro m n ε c t p q e sL ρ hL R _ y H hH
  refine ⟨⟨nG hH, unif_family (sL R) (sL (DN ε t H R)) (hL.cont R) (hL.cont _) (nG hH) (cont_nG hH) (nG_zero hH)
    (fun g hg s => hN m n ε c t p q e sL ρ hL R H hH (nG hH) (mR_nG hH) g hg s) y⟩,
    ⟨mG hH, unif_family (sL R) (sL (DM ε c H R)) (hL.cont R) (hL.cont _) (mG hH) (cont_mG hH) (mG_zero hH)
    (fun g hg s => hM m n ε c t p q e sL ρ hL R H hH (mG hH) (mR_mG hH) g hg s) y⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDN

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem gs_norm (c : ℝ) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]

theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs
  fun_prop

theorem integrable_poly_gs (P : PX m n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ‖evX P x‖ * ‖gs c x‖) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  obtain ⟨Cp, k, hCp, hP⟩ := poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := decay k c hc r
  refine Integrable.mono' ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume)
    (r := r) (by rw [hr]; linarith)).const_mul (Cp * Cd))
    (((continuous_evX P).norm.mul (continuous_gs c).norm).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hg : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
    rw [gs_norm]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (sq_norm_le_sum x) hc.le))
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (Cp * (1 + ‖x‖) ^ k) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hP x) hg (norm_nonneg _) (by positivity)
    _ = Cp * ((1 + ‖x‖) ^ k * Real.exp (-(c * ‖x‖ ^ 2))) := by ring
    _ ≤ Cp * (Cd * (1 + ‖x‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hx0) hCp
    _ = Cp * Cd * (1 + ‖x‖) ^ (-r) := by ring

def trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Qp ε j i

theorem evX_trH (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (trH ε H) x = (H * gramX ε x).trace := by
  simp only [trH, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX, evX, map_sum, map_mul,
    MvPolynomial.eval_C]

theorem evX_DN (ε : Fin m → Bool) (t : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (x : Fin m → Fin n → ℂ) :
    evX (DN ε t H R) x = Complex.I * t * (H * gramX ε x).trace * evX R x := by
  have h : evX (DN ε t H R) x = (Complex.I * t) * evX (trH ε H) x * evX R x := by
    simp only [DN, trH, evX, map_mul, MvPolynomial.eval_C]
  rw [h, evX_trH]

theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_evX _

private theorem norm_evX_gs_exp_trace_eq_of_isHermitian (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (x : Fin m → Fin n → ℂ) :
    ‖evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace)‖ =
      ‖evX P x‖ * ‖gs c x‖ := by
  rw [norm_mul, norm_mul, norm_phase t _ (trace_im ε x hB), mul_one]
private theorem continuous_evX_gs_exp_trace (ε : Fin m → Bool) (c t : ℝ) (P : PX m n)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin m → Fin n → ℂ =>
      evX P x * gs c x * Complex.exp (Complex.I * t * (B * gramX ε x).trace) :=
  ((continuous_evX P).mul (continuous_gs c)).mul (Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))
private theorem isHermitian_add_real_smul {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (hH : H.IsHermitian) (σ : ℝ) : (b + (σ : ℂ) • H).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]

theorem hasDerivAt_secN (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) (R : PX m n)
    {b H : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hH : H.IsHermitian) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => secN ε c t R (b + (σ : ℂ) • H)) (secN ε c t (DN ε t H R) (b + (s : ℂ) • H)) s := by
  have hB : ∀ σ : ℝ, (b + (σ : ℂ) • H).IsHermitian := fun σ => isHermitian_add_real_smul hb hH σ
  have hd : ∀ (x : Fin m → Fin n → ℂ) (σ : ℝ),
      HasDerivAt (fun τ : ℝ => evX R x * gs c x *
          Complex.exp (Complex.I * t * ((b + (τ : ℂ) • H) * gramX ε x).trace))
        (evX (DN ε t H R) x * gs c x *
          Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace)) σ := by
    intro x σ
    have htr : ∀ τ : ℝ, ((b + (τ : ℂ) • H) * gramX ε x).trace =
        (b * gramX ε x).trace + (τ : ℂ) * (H * gramX ε x).trace := by
      intro τ
      rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    simp only [htr]
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * t * ((b * gramX ε x).trace +
        (τ : ℂ) * (H * gramX ε x).trace)) (Complex.I * t * (H * gramX ε x).trace) σ := by
      refine (((((hasDerivAt_id σ).ofReal_comp).mul_const ((H * gramX ε x).trace)).const_add
        ((b * gramX ε x).trace)).const_mul (Complex.I * t)).congr_deriv ?_
      simp
    refine (h1.cexp.const_mul (evX R x * gs c x)).congr_deriv ?_
    rw [evX_DN]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
    (F := fun σ : ℝ => fun x => evX R x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (F' := fun σ : ℝ => fun x => evX (DN ε t H R) x * gs c x *
      Complex.exp (Complex.I * t * ((b + (σ : ℂ) • H) * gramX ε x).trace))
    (x₀ := s) (s := Set.univ) (bound := fun x => ‖evX (DN ε t H R) x‖ * ‖gs c x‖)
    Filter.univ_mem
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable)
    (Integrable.mono' (integrable_poly_gs R hc) (continuous_evX_gs_exp_trace ε c t R _).aestronglyMeasurable
      (Eventually.of_forall fun x => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t R (hB s) x).le))
    (continuous_evX_gs_exp_trace ε c t _ _).aestronglyMeasurable
    (Eventually.of_forall fun x σ _ => (norm_evX_gs_exp_trace_eq_of_isHermitian ε c t _ (hB σ) x).le)
    (integrable_poly_gs _ hc)
    (Eventually.of_forall fun x σ _ => hd x σ)
  exact key.2

theorem sec_along {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
    {ρ : GR n → PX m n →ₗ[ℂ] PX m n} (hL : LocData ε c t p q e sL ρ) {C : ℂ}
    (hcell : ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sL P g = C * secN ε c t P b)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) {f : ℝ → GR n} (hf : ∀ σ : ℝ, mR (f σ) = nU ((σ : ℂ) • H))
    {y₁ w : GR n} {b : Matrix (Fin n) (Fin n) ℂ} (hy₁ : IsUp y₁) (hb : b.IsHermitian) (hw : mR w = JJ n * nU b)
    (P : PX m n) (σ : ℝ) : sL P (y₁ * w * f σ) = F0 p q e y₁ * (C * secN ε c t P (b + (σ : ℂ) • H)) := by
  have hfw : mR (w * f σ) = JJ n * nU (b + (σ : ℂ) • H) := by
    rw [mR_mul, hw, hf, Matrix.mul_assoc, nU_mul_nU]
  have hbσ : (b + (σ : ℂ) • H).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hb.eq, hH.eq, Complex.star_def, Complex.conj_ofReal]
  rw [mul_assoc, hL.law P y₁ (w * f σ) hy₁, hcell P (w * f σ) _ hbσ hfw]

end PositivityTheory.Rg.Sw.AbsSt.SDN

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.DF PositivityTheory.Rg.Sw.AbsSt.SDN

theorem nDer : NDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨y₁, w, b, hy₁, hb, hw, rfl⟩ := cell_dec g hg
  obtain ⟨C, -, hcell⟩ := hL.cell
  have hfun : (fun σ : ℝ => sL R (y₁ * w * f σ)) =
      fun σ : ℝ => F0 p q e y₁ * (C * secN ε c t R (b + (σ : ℂ) • H)) :=
    funext fun σ => sec_along hL hcell hH hf hy₁ hb hw R σ
  rw [hfun, sec_along hL hcell hH hf hy₁ hb hw (DN ε t H R) s]
  exact ((hasDerivAt_secN ε hL.cpos t R hb hH s).const_mul C).const_mul _

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem coV : CoV := by
  intro m n A hA F
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = mulR A y := by
    intro y; funext a j
    simp [L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hdetLi : LinearMap.det Li = Complex.normSq A.det := by
    simp only [Li]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]
  have hdet : LinearMap.det L = Complex.normSq A.det ^ m := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : 0 < Complex.normSq A.det ^ m := pow_pos (Complex.normSq_pos.2 hA) _
  have hne : LinearMap.det L ≠ 0 := by rw [hdet]; exact hD.ne'
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.equivOfDetNeZero L hne
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = mulR A y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  have h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x := by
    have := integral_map_equiv e F (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem aE_eq (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ = NormedSpace.exp (σ • H) := by
  unfold aE; rw [Complex.coe_smul]

theorem hasDerivAt_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun σ : ℝ => aE H σ i j) ((aE H s * H) i j) s := by
  simp only [aE_eq]
  open scoped Matrix.Norms.Operator in
  exact ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)

theorem mulR_mul (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    mulR B (mulR A y) = mulR (A * B) y := by
  funext a j
  simp only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem mulR_one (y : Fin m → Fin n → ℂ) : mulR (1 : Matrix (Fin n) (Fin n) ℂ) y = y := by
  funext a j
  simp [mulR, Matrix.one_apply]

theorem hasDerivAt_mulR (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    HasDerivAt (fun σ : ℝ => mulR (aE H σ) y a j) (mulR H (mulR (aE H s) y) a j) s := by
  have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)
  have e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j := by
    rw [mulR_mul]; rfl
  exact e ▸ h

theorem hasDerivAt_ept (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun σ : ℝ => ept (mulR (aE H σ) y) k) (ept (mulR H (mulR (aE H s) y)) k) s := by
  rcases k with ⟨a, j, b⟩
  cases b
  · exact hasDerivAt_mulR H y s a j
  · exact (hasDerivAt_mulR H y s a j).star

theorem evX_eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (eulH H R) z = ∑ k, MvPolynomial.eval (ept z) (pderiv k R) * ept (mulR H z) k := by
  simp only [eulH, evX_eq, map_sum, map_add, map_mul, eval_X, eval_C]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']
  ring_nf

def trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)

theorem evX_Qb_add (ε : Fin m → Bool) (z : Fin m → Fin n → ℂ) (i j : Fin n) :
    evX (Qb ε true i j + Qb ε false i j) z = ∑ a, star (z a i) * z a j := by
  simp only [Qb, evX_eq, map_add, map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]
  convert Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3
  ext x; simp

theorem evX_trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin m → Fin n → ℂ) :
    evX (trHQ ε H) z = ∑ a, ∑ j, star (z a j) * mulR H z a j := by
  have e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z := by
    simp only [trHQ, evX_eq, map_sum, map_mul, eval_C]
  rw [e]
  simp only [evX_Qb_add, mulR, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ a, H i j * (star (z a j) * z a i) = ∑ j, ∑ i, ∑ a, H i j * (star (z a j) * z a i) :=
        Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, star (z a j) * (z a i * H i j) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem trHQ_real (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (z : Fin m → Fin n → ℂ) :
    (evX (trHQ ε H) z).im = 0 := by
  have hij : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z := by
    rw [evX_trHQ]
    simp only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ j, ∑ i, z a j * (star (z a i) * H j i) = ∑ i, ∑ j, z a j * (star (z a i) * H j i) := Finset.sum_comm
      _ = ∑ i, ∑ j, star (z a i) * (z a j * H j i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem hasDerivAt_normSq (w : ℝ → ℂ) (w' : ℂ) (s : ℝ) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun σ => ‖w σ‖ ^ 2) (2 * (star (w s) * w').re) s := by
  have hre : HasDerivAt (fun σ => (w σ).re) w'.re s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw
  have him : HasDerivAt (fun σ => (w σ).im) w'.im s := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw
  have h := (hre.pow 2).add (him.pow 2)
  have e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2 := fun σ => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem hasDerivAt_gsE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => gs c (mulR (aE H σ) y))
      (gs c (mulR (aE H s) y) * (-(2 * (c : ℂ)) * evX (trHQ ε H) (mulR (aE H s) y))) s := by
  have hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2)
      (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)
  have hg := (((hS.const_mul c).ofReal_comp).neg).cexp
  set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef
  have h0 : T.im = 0 := trHQ_real ε hH _
  have hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re := by
    rw [hTdef, evX_trHQ]
    simp only [Complex.re_sum, Finset.mul_sum]
  have hT' : ((T.re : ℝ) : ℂ) = T := Complex.ext (by simp) (by simp [h0])
  unfold gs
  refine hg.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [hsum]
  push_cast
  rw [hT']
  ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem aE_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [aE, neg_smul]

theorem aE_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) * aE H σ = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_mul_neg' (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ * aE H (-σ) = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (aE H σ)ᴴ = aE H σ := by
  rw [aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp

theorem det_aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : (aE H σ).det = Complex.exp ((σ : ℂ) * H.trace) := by
  rw [aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]

private theorem JJ_mul_self_eq_neg_one (n : ℕ) : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
private theorem mul_JJ_mul_conjTranspose_eq_JJ_of_inG {n : ℕ} (G Gi : M2 n) (hGi : G * Gi = 1) (hG : InG G) :
    G * JJ n * Gᴴ = JJ n := by
  have hJ := JJ_mul_self_eq_neg_one n
  have h1 : Gᴴ * JJ n = JJ n * Gi := by
    calc Gᴴ * JJ n = Gᴴ * JJ n * (G * Gi) := by rw [hGi, Matrix.mul_one]
      _ = (Gᴴ * JJ n * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = JJ n * Gi := by rw [hG]
  calc G * JJ n * Gᴴ = G * JJ n * Gᴴ * (JJ n * (-JJ n)) := by
        rw [Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]
    _ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]
    _ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = JJ n := by
        rw [hJ]
        simp [hGi]
private theorem exists_GR_mR_eq_of_inG_of_inverse {n : ℕ} (M Mi : M2 n) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hM : InG M) : ∃ x : GR n, mR x = M ∧ mR x⁻¹ = Mi :=
  ⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩
private theorem inG_JJ_mul_nU_of_isHermitian {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) (hc : c.IsHermitian) :
    InG (JJ n * nU c) := by
  unfold InG JJ nU
  rw [fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc.eq]
private theorem inG_fromBlocks_diag_of_hermitian_inverse {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (ha : a.IsHermitian)
    (ha' : a'.IsHermitian) (h : a * a' = 1) (h' : a' * a = 1) :
    InG (fromBlocks a' 0 0 a) := by
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]
  simp [h, h']

theorem cellM : CellM := by
  intro n H hH f hf g hC
  have hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g))
      (toBlocks₂₂ (mR g)) := (fromBlocks_toBlocks _).symm
  set A := toBlocks₁₁ (mR g)
  set B := toBlocks₁₂ (mR g)
  set C := toBlocks₂₁ (mR g)
  set D := toBlocks₂₂ (mR g)
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hgi : mR g * mR g⁻¹ = 1 := congrArg mR (mul_inv_cancel g)
  have hgJ : mR g * JJ n * (mR g)ᴴ = JJ n := mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2
  have hCD : C * Dᴴ = D * Cᴴ := by
    have h22 := congrArg toBlocks₂₂ hgJ
    rw [hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h22
    simp at h22
    exact ((neg_add_eq_zero).mp h22).symm
  have hCHu : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCu.star
  have hbH : (C⁻¹ * D).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]
      _ = C⁻¹ * D := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]
  have hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1 := by
    intro c
    constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp
  have hJ := JJ_mul_self_eq_neg_one n
  have hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ,
      JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1 := by
    intro c
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ,
        neg_neg]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul,
        (hnU c).2]
  obtain ⟨w₀, hw₀, hw₀i⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2
    (inG_JJ_mul_nU_of_isHermitian _ hbH)
  refine ⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩
  · show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0
    rw [hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ hCu]
  intro p q e σ
  have h1 : aE H σ * aE H (-σ) = 1 := aE_mul_neg' H σ
  have h2 : aE H (-σ) * aE H σ = 1 := aE_mul_neg H σ
  have ha : (aE H σ).IsHermitian := aE_herm hH σ
  have ha' : (aE H (-σ)).IsHermitian := aE_herm hH (-σ)
  have hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]
  obtain ⟨mA, hmA, -⟩ := exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ))
    (fromBlocks (aE H σ) 0 0 (aE H (-σ)))
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (inG_fromBlocks_diag_of_hermitian_inverse _ _ ha ha' h1 h2)
  obtain ⟨w, hw, -⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1
    (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)
  refine ⟨mA, w, ?_, ?_, hw, hc, ?_⟩
  · show toBlocks₂₁ (mR mA) = 0
    rw [hmA]
    simp
  · unfold F0 f0 u1 u2
    rw [hmA]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero,
      det_fromBlocks_zero₂₁]
    rw [← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · apply Subtype.ext
    apply Units.ext
    show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w
    rw [hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]
    congr 1
    change fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _
    rw [← aE_neg, nU, nU, JJ, fromBlocks_neg]
    simp [fromBlocks_multiply, ← Matrix.mul_assoc, h1]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem hasDerivAt_phiE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (R : PX m n)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y))
      (evX (DMp ε c H R) (mulR (aE H s) y) * gs c (mulR (aE H s) y)) s := by
  have hR : HasDerivAt (fun σ => evX R (mulR (aE H σ) y)) (evX (eulH H R) (mulR (aE H s) y)) s := by
    rw [evX_eulH]
    exact hasDerivAt_eval_curve R (fun σ => ept (mulR (aE H σ) y)) _ s
      (fun k => hasDerivAt_ept H y s k)
  refine (hR.mul (hasDerivAt_gsE c ε hH y s)).congr_deriv ?_
  simp only [DMp, trHQ, evX_eq, map_sub, map_mul, MvPolynomial.eval_C]
  ring

theorem norm_mulR_le (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    ‖mulR A y‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  calc ‖mulR A y a j‖ = ‖∑ i, y a i * A i j‖ := rfl
    _ ≤ ∑ i, ‖y a i * A i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖y‖ * ‖A i j‖ := by
        gcongr with i
        rw [norm_mul]
        gcongr
        exact (norm_le_pi_norm (y a) i).trans (norm_le_pi_norm y a)
    _ = ‖y‖ * ∑ i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ ≤ ‖y‖ * ∑ i, ∑ j, ‖A i j‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ = _ := mul_comm _ _

theorem continuous_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : Continuous fun σ : ℝ => aE H σ i j :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_aE_entry H s i j).continuousAt

theorem dom_boundE (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (P : PX m n) (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨Cp, k, hCp, hP⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound P
  obtain ⟨Cd, hCd, hdec⟩ := PositivityTheory.Rg.Sw.AbsSt.DF.decay k c hc r
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := s - 1) (b := s + 1)).exists_bound_of_continuousOn
    (f := fun σ : ℝ => ∑ i, ∑ j, ‖aE H (-σ) i j‖)
    (Continuous.continuousOn (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((continuous_aE_entry H i j).comp continuous_neg).norm))
  set L' := max L 1 with hL'
  have hL'1 : 1 ≤ L' := le_max_right _ _
  have hL'0 : 0 ≤ L' := by linarith
  refine ⟨Cp * Cd * L' ^ r, mul_nonneg (mul_nonneg hCp hCd) (Real.rpow_nonneg hL'0 r),
    fun σ hσ y => ?_⟩
  set z := mulR (aE H σ) y with hz
  have hσI : σ ∈ Icc (s - 1) (s + 1) := by
    rw [abs_lt] at hσ
    constructor <;> linarith [hσ.1, hσ.2]
  have hsum : ∑ i, ∑ j, ‖aE H (-σ) i j‖ ≤ L' := by
    have := hL σ hσI
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hy : ‖y‖ ≤ L' * ‖z‖ := by
    have hyz : y = mulR (aE H (-σ)) z := by rw [hz, mulR_mul, aE_mul_neg', mulR_one]
    calc ‖y‖ = ‖mulR (aE H (-σ)) z‖ := by rw [← hyz]
      _ ≤ (∑ i, ∑ j, ‖aE H (-σ) i j‖) * ‖z‖ := norm_mulR_le _ _
      _ ≤ L' * ‖z‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hg : ‖gs c z‖ ≤ Real.exp (-(c * ‖z‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (PositivityTheory.Rg.Sw.AbsSt.DF.sq_norm_le_sum z) hc.le))
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hmain : ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := by
    rw [norm_mul]
    calc ‖evX P z‖ * ‖gs c z‖ ≤ (Cp * (1 + ‖z‖) ^ k) * Real.exp (-(c * ‖z‖ ^ 2)) :=
          mul_le_mul (hP z) hg (norm_nonneg _) (by positivity)
      _ = Cp * ((1 + ‖z‖) ^ k * Real.exp (-(c * ‖z‖ ^ 2))) := by ring
      _ ≤ Cp * (Cd * (1 + ‖z‖) ^ (-r)) := mul_le_mul_of_nonneg_left (hdec _ hz0) hCp
      _ = _ := by ring
  have hcmp : (1 + ‖z‖) ^ (-r) ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := by
    have h1 : 1 + ‖y‖ ≤ L' * (1 + ‖z‖) := by nlinarith
    have h2 : (L' * (1 + ‖z‖)) ^ (-r) ≤ (1 + ‖y‖) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.mul_rpow hL'0 (by positivity)] at h2
    calc (1 + ‖z‖) ^ (-r) = L' ^ r * (L' ^ (-r) * (1 + ‖z‖) ^ (-r)) := by
          rw [← mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ L' ^ r * (1 + ‖y‖) ^ (-r) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hL'0 r)
  calc ‖evX P z * gs c z‖ ≤ Cp * Cd * (1 + ‖z‖) ^ (-r) := hmain
    _ ≤ Cp * Cd * (L' ^ r * (1 + ‖y‖) ^ (-r)) :=
        mul_le_mul_of_nonneg_left hcmp (mul_nonneg hCp hCd)
    _ = _ := by ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem gram_eq (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) :
    gramX ε x = (Matrix.of x)ᴴ * diagonal (sgn ε) * Matrix.of x := by
  ext i j
  rw [gramX_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gramX_mulR (ε : Fin m → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    gramX ε (mulR A y) = Aᴴ * gramX ε y * A := by
  have e : Matrix.of (mulR A y) = Matrix.of y * A := by
    ext a j; simp [mulR, Matrix.mul_apply]
  rw [gram_eq, gram_eq, e, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem trace_herm_re {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : ((H.trace.re : ℝ) : ℂ) = H.trace := by
  have him : H.trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hH.apply i i)
  exact Complex.ext (by simp) (by simp [him])

def Psi (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) : ℂ :=
  ∫ y, evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) * Complex.exp (Complex.I * t * (b * gramX ε y).trace)

theorem secN_aE (ε : Fin m → Bool) (c t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (b : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (σ : ℝ) :
    secN ε c t R (aE H (-σ) * b * aE H (-σ)) =
      Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) * Psi ε c t H b R σ := by
  have hdet : (aE H σ).det ≠ 0 := by
    rw [det_aE]
    exact Complex.exp_ne_zero _
  have hr : Complex.normSq (aE H σ).det ^ m = Real.exp (2 * m * σ * H.trace.re) := by
    rw [det_aE, Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast
    ring
  unfold secN Psi
  rw [coV m n (aE H σ) hdet, hr, Complex.ofReal_exp]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gramX_mulR, aE_herm hH]
  have e1 : aE H (-σ) * b * aE H (-σ) * (aE H σ * gramX ε y * aE H σ) =
      aE H (-σ) * (b * gramX ε y * aE H σ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (aE H (-σ)) (aE H σ), aE_mul_neg, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, aE_mul_neg', Matrix.mul_one]

private theorem continuous_evX_gs_exp_trace_mulR_aE (ε : Fin m → Bool) (c t : ℝ) (H b : Matrix (Fin n) (Fin n) ℂ)
    (P : PX m n) (σ : ℝ) :
    Continuous fun y : Fin m → Fin n → ℂ => evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  have hm : Continuous fun y : Fin m → Fin n → ℂ => mulR (aE H σ) y := by
    unfold mulR
    refine continuous_pi fun a => continuous_pi fun j => ?_
    exact continuous_finset_sum _ fun i _ =>
      (((continuous_apply i).comp (continuous_apply a) :
        Continuous fun y : Fin m → Fin n → ℂ => y a i)).mul continuous_const
  refine (((continuous_evX P).comp hm).mul ((continuous_gs c).comp hm)).mul ?_
  exact Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace))

private theorem exists_norm_evX_gs_exp_le_polynomial_decay (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (P : PX m n)
    (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, |σ - s| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
          Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨K, hK0, hK⟩ := dom_boundE c hc H P s
  refine ⟨K, hK0, fun σ hσ y => ?_⟩
  have hE : ‖Complex.exp (Complex.I * t * (b * gramX ε y).trace)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, trace_im ε y hb]
  rw [norm_mul, hE, mul_one]
  exact hK σ hσ y

theorem hasDerivAt_Psi (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (R : PX m n) (s : ℝ) :
    HasDerivAt (Psi ε c t H b R) (Psi ε c t H b (DMp ε c H R) s) s ∧
      ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
        Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hd : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℕ) : ℝ) <
      (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 := by linarith
  have hint : ∀ P : PX m n, Integrable fun y => evX P (mulR (aE H s) y) * gs c (mulR (aE H s) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace) := by
    intro P
    obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb P s
    exact ((integrable_one_add_norm hd).const_mul K).mono'
      (continuous_evX_gs_exp_trace_mulR_aE ε c t H b P s).aestronglyMeasurable
      (ae_of_all _ fun y => hK s (by simp) y)
  refine ⟨?_, hint⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_evX_gs_exp_le_polynomial_decay ε hc t H hb (DMp ε c H R) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ y => evX R (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (F' := fun σ y => evX (DMp ε c H R) (mulR (aE H σ) y) * gs c (mulR (aE H σ) y) *
      Complex.exp (Complex.I * t * (b * gramX ε y).trace))
    (bound := fun y => K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)))
    (x₀ := s) (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun σ => (continuous_evX_gs_exp_trace_mulR_aE ε c t H b R σ).aestronglyMeasurable)
    (hint R) (continuous_evX_gs_exp_trace_mulR_aE ε c t H b (DMp ε c H R) s).aestronglyMeasurable
    (ae_of_all _ fun y σ hσ => hK σ (by rwa [Metric.mem_ball, Real.dist_eq] at hσ) y)
    ((integrable_one_add_norm hd).const_mul K)
    (ae_of_all _ fun y σ _ => (hasDerivAt_phiE c ε hH R y σ).mul_const _)
  exact key.2

theorem evX_DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (DM ε c H R) z = ((m : ℂ) * H.trace) * evX R z + evX (DMp ε c H R) z := by
  have h : DM ε c H R = C ((m : ℂ) * H.trace) * R + DMp ε c H R := by
    simp only [DM, DMp]
    ring
  rw [h, evX_eq, evX_eq, evX_eq, map_add, map_mul, eval_C]

end PositivityTheory.Rg.Sw.AbsSt.SDM

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SDM

theorem mDer : MDer := by
  intro m n ε c t p q e sL ρ hL R H hH f hf g hg s
  obtain ⟨C0, -, hcell⟩ := hL.cell
  obtain ⟨y₁, b, hy₁, hb, hdec⟩ := cellM n H hH f hf g hg
  have hpq : (p : ℂ) + q = m := by
    rcases hL.sign with ⟨_, hp, hq⟩ | ⟨_, hp, hq⟩
    · rw [hp, hq]
      exact_mod_cast DF.cnt_add ε
    · rw [hp, hq, add_comm]
      exact_mod_cast DF.cnt_add ε
  have hrep : ∀ (P : PX m n) (σ : ℝ), sL P (g * f σ) =
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b P σ) := by
    intro P σ
    obtain ⟨mA, w, hmA, hF0, hw, hb', heq⟩ := hdec p q e σ
    have hex : Complex.exp (-(↑σ * ↑(p + q) * H.trace)) *
        Complex.exp (((2 * m * σ * H.trace.re : ℝ) : ℂ)) = Complex.exp (↑σ * (↑m * H.trace)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [trace_herm_re hH]
      linear_combination (-(σ : ℂ) * H.trace) * hpq
    rw [heq, mul_assoc y₁ mA w, hL.law P y₁ _ hy₁, hL.law P mA w hmA, hcell P w _ hb' hw,
      secN_aE ε c t hH b P σ, hF0, ← hex]
    ring
  have hΨ := hasDerivAt_Psi ε hL.cpos t hH hb R s
  have hE : HasDerivAt (fun σ : ℝ => Complex.exp (↑σ * (↑m * H.trace)))
      (Complex.exp (↑s * (↑m * H.trace)) * (↑m * H.trace)) s := by
    have h1 := ((hasDerivAt_id s).ofReal_comp.mul_const ((m : ℂ) * H.trace)).cexp
    simpa using h1
  have hfun : (fun σ : ℝ => sL R (g * f σ)) = fun σ =>
      F0 p q e y₁ * C0 * (Complex.exp (↑σ * (↑m * H.trace)) * Psi ε c t H b R σ) := funext (hrep R)
  have hlin : Psi ε c t H b (DM ε c H R) s =
      (↑m * H.trace) * Psi ε c t H b R s + Psi ε c t H b (DMp ε c H R) s := by
    unfold Psi
    rw [← integral_const_mul, ← integral_add ((hΨ.2 R).const_mul _) (hΨ.2 _)]
    congr 1
    funext y
    rw [evX_DM]
    ring
  rw [hfun, hrep (DM ε c H R) s, hlin]
  exact ((hE.mul hΨ.1).const_mul (F0 p q e y₁ * C0)).congr_deriv (by ring)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def gen (ε : Fin m → Bool) (k : Bool × Fin n × Fin n) : PX m n := Qb ε k.1 k.2.1 k.2.2

def Mon (ε : Fin m → Bool) (d : ℕ) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {M | ∃ l : List (Bool × Fin n × Fin n), l.length ≤ d ∧ M = (l.map (gen ε)).prod}

theorem mon_mono (ε : Fin m → Bool) {d d' : ℕ} (h : d ≤ d') : Mon (n := n) ε d ≤ Mon ε d' :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem gen_mul_mon (ε : Fin m → Bool) (d : ℕ) (k : Bool × Fin n × Fin n) {M : PX m n} (hM : M ∈ Mon ε d) :
    gen ε k * M ∈ Mon ε (d + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mon_mul (ε : Fin m → Bool) {d d' : ℕ} {a b : PX m n} (ha : a ∈ Mon ε d) (hb : b ∈ Mon ε d') :
    a * b ∈ Mon ε (d + d') := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      exact Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

theorem adjoin_le (ε : Fin m → Bool) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) :
    ∃ d, R ∈ Mon ε d := by
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mon_mul ε hd hd'⟩

theorem dsum_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (x : PX m n) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

def eulD (H : Matrix (Fin n) (Fin n) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) • pderiv (a, j, false) +
    (∑ i, X (a, i, true) * C (star (H i j))) • pderiv (a, j, true))

theorem eulH_eq (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : eulH H R = eulD H R := by
  simp [eulH, eulD, dsum_apply, smul_eq_mul]

theorem eulD_X_false (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, false) : PX m n) = ∑ i, X (a, i, false) * C (H i j) := by
  simp [eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulD_X_true (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, true) : PX m n) = ∑ i, X (a, i, true) * C (star (H i j)) := by
  simp [eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulH_gen (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (k : Bool × Fin n × Fin n) :
    eulH H (gen ε k) ∈ Mon ε 1 := by
  have : eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2) := by
    obtain ⟨b, i, j⟩ := k
    rw [eulH_eq]
    simp only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  refine add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)

theorem eulH_mon (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) {M : PX m n} (hM : M ∈ Mon ε d) :
    eulH H M ∈ Mon ε d := by
  rw [eulH_eq]
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction l generalizing d with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]
      simp only [List.length_cons] at hl
      have hd : l.length + 1 ≤ d := hl
      refine add_mem ?_ ?_
      · exact mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))
      · have h1 := eulH_gen ε H k
        rw [eulH_eq] at h1
        have h2 : (l.map (gen ε)).prod ∈ Mon ε l.length := Submodule.subset_span ⟨l, le_rfl, rfl⟩
        rw [mul_comm ((l.map (gen ε)).prod)]
        exact mon_mono ε (by omega) (mon_mul ε h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(eulD H).map_smul]; exact Submodule.smul_mem _ _ hx

end PositivityTheory.Rg.Sw.AbsSt.CycP
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

def secK (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) : C(KR n, ℂ) :=
  ⟨fun k => sL R ((k : GR n) * y), (hL.cont R).comp (continuous_subtype_val.mul continuous_const)⟩

@[simp] theorem secK_apply (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) (k : KR n) :
    secK hL R y k = sL R ((k : GR n) * y) := rfl

def Ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) : Submodule ℂ (PX m n) where
  carrier := {R | ∀ y, L (secK hL R y) = 0}
  add_mem' := by
    intro R R' hR hR' y
    have : secK hL (R + R') y = secK hL R y + secK hL R' y := by ext k; simp
    rw [this, map_add, hR y, hR' y, add_zero]
  zero_mem' := by
    intro y
    have : secK hL 0 y = 0 := by ext k; simp
    rw [this, map_zero]
  smul_mem' := by
    intro a R hR y
    have : secK hL (a • R) y = a • secK hL R y := by ext k; simp
    rw [this, map_smul, hR y, smul_zero]

theorem ann_of_quot (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) {R D : PX m n} (hR : R ∈ Ann hL L)
    (hq : ∀ y : GR n, ∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL D ((k : GR n) * y)‖ ≤ δ) :
    D ∈ Ann hL L := by
  intro y
  have hR' : ∀ y', L (secK hL R y') = 0 := hR
  obtain ⟨f, hf⟩ := hq y
  set F : ℝ → C(KR n, ℂ) := fun s => (s : ℂ)⁻¹ • (secK hL R (y * f s) - secK hL R y) with hF
  have hU : TendstoUniformly (fun s (k : KR n) => F s k) (secK hL D y) (𝓝[≠] (0:ℝ)) := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨η, hη, hs⟩ := hf (δ / 2) (by linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨η, hη, ?_⟩
    intro s hs1 hs2 k
    have hs0 : s ≠ 0 := hs2
    have habs : |s| < η := by simpa [Real.dist_eq] using hs1
    have hk := hs s hs0 habs k
    rw [dist_comm, dist_eq_norm]
    have e : F s k = (sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s := by
      simp [hF, secK_apply, mul_assoc, div_eq_inv_mul]
    rw [e, secK_apply]
    linarith
  have hT : Filter.Tendsto F (𝓝[≠] (0:ℝ)) (𝓝 (secK hL D y)) :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr (fun K _ => hU.tendstoUniformlyOn)
  have hL0 : Filter.Tendsto (fun s => L (F s)) (𝓝[≠] (0:ℝ)) (𝓝 (L (secK hL D y))) :=
    (L.continuous.tendsto _).comp hT
  have hz : (fun s => L (F s)) = fun _ => (0 : ℂ) := by
    funext s
    simp only [hF, map_smul, map_sub, hR' (y * f s), hR' y, sub_self, smul_zero]
  rw [hz] at hL0
  exact tendsto_nhds_unique hL0 tendsto_const_nhds

theorem t_ne (hL : LocData ε c t p q e sL ρ) : t ≠ 0 := by
  intro h0
  have hc := hL.cpos
  rcases hL.sign with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

def lin (Φ : Fin n → Fin n → PX m n) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Φ j i

theorem lin_add (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H + H') = lin Φ H + lin Φ H' := by
  simp only [lin, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem lin_sub (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H - H') = lin Φ H - lin Φ H' := by
  simp only [lin, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lin_smul (Φ : Fin n → Fin n → PX m n) (z : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) : lin Φ (z • H) = z • lin Φ H := by
  simp only [lin, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem lin_single (Φ : Fin n → Fin n → PX m n) (a b : Fin n) :
    lin Φ (Matrix.single a b (1 : ℂ)) = Φ b a := by
  classical
  simp [lin, Matrix.single_apply, ite_and, apply_ite C, ite_mul, Finset.sum_ite_eq]

theorem herm1 (a b : Fin n) : (Matrix.single a b (1 : ℂ) + Matrix.single b a 1).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, add_comm]

theorem herm2 (a b : Fin n) : (Complex.I • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
    star_one, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem entry_of_lin (S : Submodule ℂ (PX m n)) (Φ : Fin n → Fin n → PX m n) (R : PX m n)
    (h : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin Φ H * R ∈ S) (a b : Fin n) :
    Φ b a * R ∈ S := by
  have h1 := h _ (herm1 a b)
  have h2 := h _ (herm2 a b)
  rw [lin_add, lin_single, lin_single] at h1
  rw [lin_smul, lin_sub, lin_single, lin_single] at h2
  have hI : (-(Complex.I / 2)) * Complex.I = (1 / 2 : ℂ) := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have h3 : Φ b a * R = (1 / 2 : ℂ) • ((Φ b a + Φ a b) * R) + (-(Complex.I / 2)) • ((Complex.I • (Φ b a - Φ a b)) * R) := by
    rw [smul_mul_assoc, smul_smul, hI, add_mul, sub_mul]
    module
  rw [h3]
  exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

theorem mon_le_adjoin (ε : Fin m → Bool) (d : ℕ) {R : PX m n} (hR : R ∈ Mon ε d) :
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have hle : Mon ε d ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) := by
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    apply Subalgebra.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  exact hle hR

theorem gen_mul_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer) (d : ℕ)
    (hd : Mon ε d ≤ Ann hL L) {R : PX m n} (hR : R ∈ Mon ε d) (k : Bool × Fin n × Fin n) :
    gen ε k * R ∈ Ann hL L := by
  have hRA : R ∈ Ann hL L := hd hR
  have hRad := mon_le_adjoin ε d hR
  have hN : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qp ε j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDN : DN ε t H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).1)
    have ht : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (t_ne hL))
    have e1 : lin (fun j i => Qp ε j i) H * R = (Complex.I * (t : ℂ))⁻¹ • DN ε t H R := by
      rw [lin, DN, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ hDN
  have hM : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qb ε true j i + Qb ε false j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDM : DM ε c H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).2)
    have hE : eulH H R ∈ Ann hL L := hd (eulH_mon ε H d hR)
    have hc : (2 * (c : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hL.cpos.ne')
    have e1 : lin (fun j i => Qb ε true j i + Qb ε false j i) H * R
        = (2 * (c : ℂ))⁻¹ • (((m : ℂ) * H.trace) • R + eulH H R - DM ε c H R) := by
      rw [lin, DM, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, sub_sub_cancel, ← mul_assoc, ← mul_assoc,
        ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ ((Ann hL L).sub_mem ((Ann hL L).add_mem ((Ann hL L).smul_mem _ hRA) hE) hDM)
  obtain ⟨b, i, j⟩ := k
  have hP := entry_of_lin (Ann hL L) (fun j i => Qp ε j i) R hN j i
  have hS := entry_of_lin (Ann hL L) (fun j i => Qb ε true j i + Qb ε false j i) R hM j i
  have hsum := (Ann hL L).add_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  have hdif := (Ann hL L).sub_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  cases b
  · convert hdif using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module
  · convert hsum using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module

theorem mon_le_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer)
    (h1 : (1 : PX m n) ∈ Ann hL L) : ∀ d, Mon ε d ≤ Ann hL L := by
  intro d
  induction d with
  | zero =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hl0
    simpa using h1
  | succ d ih =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    cases l with
    | nil => simpa using h1
    | cons a l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
      rw [List.map_cons, List.prod_cons]
      have hM : (List.map (gen ε) l).prod ∈ Mon ε d := Submodule.subset_span ⟨l, hl, rfl⟩
      exact gen_mul_ann hL L hD d ih hM a

end PositivityTheory.Rg.Sw.AbsSt.CycP

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.CycP

theorem cycSec_of (hC : Cyc) (hZ : SecZero) (hD : SecDer) : CycSec := by
  intro m n ε c t p q e sL ρ hL L hL0 P h hh
  have h1 : (1 : PX m n) ∈ Ann hL L := by
    intro y
    refine hL0 y _ fun k => ?_
    simp [hL.vac]
  obtain ⟨R, hR, hPR⟩ := hC m n ε c hL.cpos P
  obtain ⟨d, hd⟩ := adjoin_le ε hR
  have hRA := mon_le_ann hL L hD h1 d hd
  have hz := (hZ m n ε c t p q e sL ρ hL (P - R)).1 hPR
  have : h = secK hL R 1 := by
    ext k
    have := hz (k : GR n)
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    rw [hh, secK_apply, mul_one, this]
  rw [this]
  exact hRA 1

end PositivityTheory.Rg.Sw.AbsSt
end
end

section
namespace PositivityTheory.Rg.Sw.AbsSt

theorem secDer : SecDer := secDer_of nDer mDer

end PositivityTheory.Rg.Sw.AbsSt
end
