import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet

section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def retV (g₀ : B.Mat k r) : Set (B.Mat k r) := {Y | IsUnit (g₀⁻¹ * Y + 1).det}

def retDom (g₀ : B.Mat k r) : Set (B.Mat k r) :=
  retV g₀ ∩ (fun Y => prj (iot (g₀⁻¹ * Y))) ⁻¹' {X | IsUnit (1 - X).det}

def ret (g₀ : B.Mat k r) (Y : B.Mat k r) : B.Mat k r := g₀ * kap (prj (iot (g₀⁻¹ * Y)))

lemma isOpen_unitDet {X : Type*} [TopologicalSpace X] {f : X → B.Mat k r} (hf : Continuous f) :
    IsOpen {x | IsUnit (f x).det} := by
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

lemma isOpen_retV (g₀ : B.Mat k r) : IsOpen (retV g₀) := isOpen_unitDet ((continuous_const.mul continuous_id).add continuous_const)

lemma cd_iotL (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (fun Y => iot (g₀⁻¹ * Y)) (retV g₀) := by
  have h1 : ContDiffOn ℝ ∞ (fun Y : B.Mat k r => g₀⁻¹ * Y) (retV g₀) := cdm_mul contDiffOn_const contDiffOn_id
  show ContDiffOn ℝ ∞ (fun Y => (g₀⁻¹ * Y - 1) * (g₀⁻¹ * Y + 1)⁻¹) (retV g₀)
  exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun Y hY => hY)

lemma isOpen_retDom (g₀ : B.Mat k r) : IsOpen (retDom g₀) := by
  exact (cdm_prj (cd_iotL g₀)).continuousOn.isOpen_inter_preimage (isOpen_retV g₀)
    (isOpen_unitDet (f := fun X : B.Mat k r => 1 - X) (continuous_const.sub continuous_id))

lemma cd_ret (g₀ : B.Mat k r) : ContDiffOn ℝ ∞ (ret g₀) (retDom g₀) := by
  have hA : ContDiffOn ℝ ∞ (fun Y => prj (iot (g₀⁻¹ * Y))) (retDom g₀) :=
    cdm_prj ((cd_iotL g₀).mono Set.inter_subset_left)
  show ContDiffOn ℝ ∞ (fun Y => g₀ * ((1 + prj (iot (g₀⁻¹ * Y))) * (1 - prj (iot (g₀⁻¹ * Y)))⁻¹)) (retDom g₀)
  exact cdm_mul contDiffOn_const
    (cdm_mul (contDiffOn_const.add hA) (cdm_inv (contDiffOn_const.sub hA) fun Y hY => hY.2))

lemma ret_mem {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ retDom g₀) :
    ret g₀ Y ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.B2x8.al_mul_mem hg₀ (kap_mem (prj_lie (iot (g₀⁻¹ * Y))) hY.2)

private lemma prj_eq_self_of_inLie {X : B.Mat k r} (hX : B.inLie k r X) : prj X = X := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX'
  have h2 : Hpk k r * Xᴴ * Hpk k r = -X := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Ux10.hpk_sq', Matrix.one_mul]
  unfold prj
  rw [h2, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

lemma ret_self {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) {Y : B.Mat k r} (hY : Y ∈ B.GV k r)
    (hu : IsUnit (g₀⁻¹ * Y + 1).det) : ret g₀ Y = Y := by
  have hh : g₀⁻¹ * Y ∈ B.GV k r := Formalism.FourierDecayAlt.P.B2x8.al_mul_mem (Formalism.FourierDecayAlt.P.B2x8.al_inv_mem hg₀) hY
  obtain ⟨hl, -, hk⟩ := iot_facts hh hu
  show g₀ * kap (prj (iot (g₀⁻¹ * Y))) = Y
  rw [prj_eq_self_of_inLie hl, hk, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀), Matrix.one_mul]

lemma self_mem_retDom {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : g₀ ∈ retDom g₀ := by
  have e : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_GV hg₀)
  refine ⟨?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1).det
    rw [e, ← two_smul ℂ (1 : B.Mat k r), Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
  · show IsUnit (1 - prj (iot (g₀⁻¹ * g₀))).det
    rw [e, show iot (1 : B.Mat k r) = 0 by simp [iot], prj_zero, sub_zero, Matrix.det_one]
    exact isUnit_one

lemma ret_at {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r) : ret g₀ g₀ = g₀ := ret_self hg₀ hg₀ (And.left (self_mem_retDom hg₀))

lemma glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

theorem smoothLev_of_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : ∀ m : ℕ, CkLev k r 0 m D f) : SmoothLev k r 0 D f := by
  intro g₀ hg₀
  have hG₀ : g₀ ∈ B.GV k r := hg₀.1.1
  have hU : IsOpen (retDom g₀ ∩ ret g₀ ⁻¹' D) :=
    (cd_ret g₀).continuousOn.isOpen_inter_preimage (isOpen_retDom g₀) hD
  refine ⟨retDom g₀ ∩ ret g₀ ⁻¹' D, fun Y => f (ret g₀ Y), hU, ⟨self_mem_retDom hG₀, ?_⟩, ?_, ?_⟩
  · show ret g₀ g₀ ∈ D
    rw [ret_at hG₀]
    exact hg₀.2
  · intro Y hY
    refine ContDiffAt.contDiffWithinAt ?_
    have hr : ContDiffAt ℝ ∞ (ret g₀) Y := (cd_ret g₀).contDiffAt ((isOpen_retDom g₀).mem_nhds hY.1)
    refine contDiffAt_infty.2 fun m => ?_
    have hZ : ret g₀ Y ∈ Glev k r 0 ∩ D := ⟨glev0 (ret_mem hG₀ hY.1), hY.2⟩
    obtain ⟨U, F, hUo, hZU, hF, hfF⟩ := hf m (ret g₀ Y) hZ
    have hc : ContDiffAt ℝ m (fun Y' => F (ret g₀ Y')) Y :=
      (hF.contDiffAt (hUo.mem_nhds hZU)).comp Y (contDiffAt_infty.1 hr m)
    refine hc.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ Y' in 𝓝 Y, Y' ∈ retDom g₀ := (isOpen_retDom g₀).mem_nhds hY.1
    have h2 : ∀ᶠ Y' in 𝓝 Y, ret g₀ Y' ∈ U := hr.continuousAt.preimage_mem_nhds (hUo.mem_nhds hZU)
    filter_upwards [h1, h2] with Y' h1' h2'
    exact hfF _ h2' (glev0 (ret_mem hG₀ h1'))
  · intro g hg hgl
    show f g = f (ret g₀ g)
    rw [ret_self hG₀ hgl.1 hg.1.1]

end Formalism.FourierDecayAlt.P5.Rad
end
end

section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma thr_big (k r m : ℕ) :
    JF.TransportedAlt k r (6 * (r : ℝ) * (m : ℝ) + 9 * ((r : ℝ) + 1) * (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1)) m := by
  unfold JF.TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r]

theorem jf_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    SmoothLev k r 0 (OmPlus k r D.z D.z') (B.JF D F) := by
  refine smoothLev_of_ck (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _) fun m => ?_
  exact (Formalism.FourierDecayAlt.P.jacquet_derivative_formula k r Wp Wq D _ m F (thr_big k r m) (hF _ m)).1

lemma μE_one (i j : ℕ) : PI.QnWCellW.μE (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j =
    if i < k + 1 ∧ j < k + 1 ∧ i = j then 1 else 0 := by
  unfold PI.QnWCellW.μE
  by_cases h : i < k + 1 ∧ j < k + 1
  · rw [dif_pos h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [h]
    · rw [if_neg (by simpa [Fin.ext_iff] using hij), if_neg (by tauto)]
  · rw [dif_neg h, if_neg (by tauto)]

theorem wCell_last_eq (c : Fin r → ℂ) : wCell k r (Fin.last r) c = bigCell k r c 1 := by
  rw [PI.QnWCellW.wCell_last]
  ext p q
  rw [PI.QnWCellW.Wm_range_apply, PI.QnWCellW.bigCell_apply]
  simp only [μE_one, PI.QnWCellW.cf, Fin.ext_iff, PI.QnWCellW.swp_val]
  have hp := p.isLt
  have hq := q.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 3; omega) | (rw [show 2 * r + k - (q : ℕ) = (p : ℕ) by omega])

lemma glev_last_uwb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := by
  exact ⟨hg.1, fun a => hg.2 a (by simp)⟩

lemma zetaL_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp only [zetaL, Formalism.FourierDecayAlt.P.Qx5.fvec_last]

theorem wCell_mem_omPlus {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    wCell k r (Fin.last r) c * g ∈ OmPlus k r z z' := by
  have hgz' : inWb k r (g *ᵥ z') := by
    intro i hi
    have hi0 := i.isLt
    rcases hi with hi | hi
    · have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (esI k r ⟨i.val, hi⟩)
      rw [← (hg.2 ⟨i.val, hi⟩ (by simpa using hi)).2, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (esI k r ⟨i.val, hi⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rfl
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inl hi)
    · have ha : 2 * r + k - i.val < r := by omega
      have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (eI k r ⟨_, ha⟩)
      rw [← (hg.2 ⟨_, ha⟩ (by simpa using ha)).1, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have hi' : esI k r ⟨_, ha⟩ = i := Fin.ext (by simp only [esI]; omega)
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (eI k r ⟨_, ha⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hi']
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inr hi)
  have hwv : ∀ v, inWb k r v → bigCell k r c 1 *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
    rw [Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
  have hZ : Zhat k r z z' (wCell k r (Fin.last r) c * g) = Matrix.diagonal fun a : Fin (r + 1) =>
      if h : a.val < r then c ⟨a.val, h⟩ else zetaL k r z z' (Fin.last r) g := by
    rw [zetaL_last, ← hwv _ hgz', ← Formalism.QuantumDeterminants.bigCellZhat k r z (g *ᵥ z') c 1 hz hgz', wCell_last_eq]
    ext a b
    simp only [Zhat]
    by_cases hb : b.val < r
    · simp only [fvec, dif_pos hb, ← mulVec_mulVec, (hg.2 ⟨b.val, hb⟩ (by simpa using hb)).1]
    · simp only [fvec, dif_neg hb, mulVec_mulVec]
  have hD := fun l => Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag z z' _ _ hZ l
  have h0 : Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = ∏ a : Fin r, c a := by
    rw [hD]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.val_castLE, a.isLt, dif_pos]
  have h1 : Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) =
      (∏ a : Fin r, c a) * zetaL k r z z' (Fin.last r) g := by
    rw [hD]
    refine (Fin.prod_univ_castSucc _).trans ?_
    congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp only [Fin.val_castLE, Fin.val_castSucc, a.isLt, dif_pos]
    · simp
  have hP : (∏ a : Fin r, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have hi : (Fin.castLE (Nat.le_of_lt_succ l.isLt) i).val < r := by
      have := i.isLt
      simp only [Fin.val_castLE]
      omega
    simp only [dif_pos hi]
    exact hc _
  · unfold Gf
    rw [h1, h0, Complex.normSq_mul]
    have hP' : 0 < Complex.normSq (∏ a : Fin r, c a) := Complex.normSq_pos.mpr hP
    have hG' := hG
    unfold GGl at hG'
    nlinarith [mul_pos hP' hG']

theorem GGl_uw {z z' : Fin (2 * r + k + 1) → ℂ} {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (g : Mx k r) : GGl k r z z' (h * g * h') = GGl k r z z' g := by
  simp only [GGl, Formalism.FourierDecayAlt.P.Qx5.zeta_inv hh hh']

theorem domR_uw {z z' : Fin (2 * r + k + 1) → ℂ} {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ DomR k r z z')
    {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    (x.1, h * x.2 * h') ∈ DomR k r z z' := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh _) h2)
      (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh' _)
  · show 0 < GGl k r z z' (h * x.2 * h')
    rw [GGl_uw hh hh']
    exact h3

theorem sf_resG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} {J : Mx k r → E}
    (hJ : SmoothLev k r 0 D J) :
    SmoothFam k r (Fin.last r) {x | x.1 ∈ OmX r ∧ wCell k r (Fin.last r) x.1 * x.2 ∈ D}
      (resG k r (Fin.last r) J) := by
  have hWs : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => wCell k r (Fin.last r) c) (OmX r) := by
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
  have hWG : ∀ c ∈ OmX r, wCell k r (Fin.last r) c ∈ Glev k r 0 := by
    intro c hc
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hG0 : ∀ x : (Fin r → ℂ) × Mx k r, x.1 ∈ OmX r → x.2 ∈ Glev k r (Fin.last r) →
      wCell k r (Fin.last r) x.1 * x.2 ∈ Glev k r 0 := fun x h1 h2 =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (hWG _ h1) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) h2)
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hJ _ ⟨hG0 x₀ hx₀.1 hg₀, hx₀.2⟩
  have hM : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => wCell k r (Fin.last r) x.1 * x.2)
      {x | x.1 ∈ OmX r} :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hWs.comp contDiffOn_fst (fun x hx => hx)) contDiffOn_snd
  have hρ : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ))
      (OmX r) := by
    have hp : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
        ∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1 : ℝ)) (OmX r) :=
      contDiffOn_prod fun a _ => by
        simp only [Fin.val_last, a.isLt, ↓reduceIte]
        exact Formalism.FourierDecayAlt.P.Qx3.cd_normPow a _
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  refine ⟨{x | x.1 ∈ OmX r} ∩ (fun x => wCell k r (Fin.last r) x.1 * x.2) ⁻¹' U,
    fun x => ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
      F (wCell k r (Fin.last r) x.1 * x.2),
    hM.continuousOn.isOpen_inter_preimage ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).preimage continuous_fst) hU,
    ⟨hx₀.1, hmem⟩, ?_, ?_⟩
  · exact (hρ.comp contDiffOn_fst (fun x hx => hx.1)).smul
      (hF.comp (hM.mono Set.inter_subset_left) (fun x hx => hx.2))
  · intro x hx hxg
    simp only [resG]
    rw [hfF _ hx.2 (hG0 x hx.1 hxg)]

end Formalism.FourierDecayAlt.P5.Rad
end
end
