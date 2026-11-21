import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousUpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangular

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem yv_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  intro k r z z' γ hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yv k r z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r r z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z' (Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z').2.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg k r z (γ * Matrix.of x.1) :=
    (LenCont.lA_Sg_continuousOn k r z).2.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset k r z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yv k r z z' γ (Matrix.of x.1) ∧ Yv k r z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  atlas_forward_decl GlobalTheory.Amp.YMeas.yv_measurable
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.Rad
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormGram

variable {k r : ℕ}

def rE (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (eI k r a)

def rW (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def rS (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (esI k r a)

def iW (k r : ℕ) (w : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ j, w j • bvec (wI k r j)

theorem iW_e (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (eI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, eI_ne_wI]
theorem middleSpaceEmbedding_apply_dualIsotropicIndex (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (esI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, esI_ne_wI]
theorem iW_w (w : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : iW k r w (wI k r j) = w j := by
  simp [iW, Finset.sum_apply, bvec_apply, wI_inj]

theorem H_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_ee, H_ew, H_es]
theorem H_w (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = sg k j * v (wI k r j) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_we, H_ww, H_ws]
theorem besselHermForm_mulVec_dualIsotropicIndex (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_se, H_sw, H_ss]

theorem herm3 (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w =
    star (rE k r w) ⬝ᵥ rS k r v + herm (Hb k) (rW k r v) (rW k r w) + star (rS k r w) ⬝ᵥ rE k r v := by
  rw [herm_Hb]
  unfold herm
  rw [dotProduct, sum3]
  simp [H_e, H_w, besselHermForm_mulVec_dualIsotropicIndex, rE, rW, rS, dotProduct]

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [← H_e v a]
  simp [bvec, dotProduct, Pi.single_apply, apply_ite]

theorem HH : Hpk k r * Hpk k r = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  unfold sg; split_ifs <;> simp_all

theorem HbHb : Hb k * Hb k = 1 := by
  unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> simp

theorem unit_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : g ∈ UH H) : IsUnit g.det := by
  have hm' : gᴴ * H * g = H := hg
  have h1 : (H * gᴴ * H) * g = 1 := by
    rw [← hH]; nth_rewrite 4 [← hm']; simp only [Matrix.mul_assoc]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem herm_iso {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hm' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm']

theorem herm_inv {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (g⁻¹ *ᵥ w) = herm (Hpk k r) (g *ᵥ v) w := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem herm_inv' {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ v) w = herm (Hpk k r) v (g *ᵥ w) := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem of_Xst {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xst k r) : rE k r v = 0 ∧ rW k r v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    constructor <;> funext j <;> simp [rE, rW, bvec_apply, eI_ne_esI, wI_ne_esI]
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    constructor <;> funext j
    · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rE]
    · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rW]
  | smul c x _ hx =>
    constructor <;> funext j
    · have := congrFun hx.1 j; simp_all [rE]
    · have := congrFun hx.2 j; simp_all [rW]

theorem mem_Xsp {v : Fin (2 * r + k + 1) → ℂ} : v ∈ Xsp k r ↔ rW k r v = 0 ∧ rS k r v = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      constructor <;> funext j <;> simp [rS, rW, bvec_apply, esI_ne_eI, wI_ne_eI]
    | zero => exact ⟨rfl, rfl⟩
    | add x y _ _ hx hy =>
      constructor <;> funext j
      · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rW]
      · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rS]
    | smul c x _ hx =>
      constructor <;> funext j
      · have := congrFun hx.1 j; simp_all [rW]
      · have := congrFun hx.2 j; simp_all [rS]
  · rintro ⟨h1, h2⟩
    have : v = ∑ a, v (eI k r a) • bvec (eI k r a) := by
      funext x
      induction x using cases3 with
      | h1 a => simp [Finset.sum_apply, bvec_apply, eI_inj]
      | h2 j => simpa [Finset.sum_apply, bvec_apply, wI_ne_eI, rW] using congrFun h1 j
      | h3 a => simpa [Finset.sum_apply, bvec_apply, esI_ne_eI, rS] using congrFun h2 a
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem of_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : rE k r z = 0 ∧ rS k r z = 0 := by
  constructor <;> funext a
  · exact hz _ (Or.inl a.2)
  · have := a.2
    exact hz _ (Or.inr (by simp only [esI]; omega))

theorem rW_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (uEmb k r u *ᵥ v) = rW k r v := by
  funext j
  have := j.2
  have h : ∀ y, uEmb k r u (wI k r j) y = if wI k r j = y then 1 else 0 := fun y => by
    unfold uEmb; rw [dif_neg (by simp only [wI]; omega), dif_neg (by simp only [wI]; omega)]
  simp [rW, Matrix.mulVec, dotProduct, h]

theorem rS_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (uEmb k r u *ᵥ v) = (u⁻¹)ᴴ *ᵥ rS k r v := by
  funext a
  have := a.2
  have hb : ∀ (b : Fin r) h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun b h =>
    Fin.ext (by have := b.2; simp only [esI]; omega)
  have h1 : ∀ b, uEmb k r u (esI k r a) (eI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_neg (by simp only [eI]; omega), if_neg (esI_ne_eI _ _)]
  have h2 : ∀ b, uEmb k r u (esI k r a) (wI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_neg (by simp only [wI]; omega), if_neg (esI_ne_wI _ _)]
  have h3 : ∀ b, uEmb k r u (esI k r a) (esI k r b) = star (u⁻¹ b a) := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_pos (by simp only [esI]; omega)]
    simp only [hb]
  simp [rS, Matrix.mulVec, dotProduct, sum3, h1, h2, h3]

theorem rW_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (pEl k r B S *ᵥ v) = rW k r v + ∑ b, rS k r v b • B b := by
  funext j
  simp [rW, rS, Matrix.mulVec, dotProduct, sum3, pEl_we, pEl_ww, pEl_ws, Finset.sum_apply, mul_comm]

theorem rS_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (pEl k r B S *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, sum3, pEl_se, pEl_sw, pEl_ss]

theorem rW_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (mEmb k r m *ᵥ v) = m *ᵥ rW k r v := by
  funext j
  simp [rW, Matrix.mulVec, dotProduct, sum3, m_we, m_ww, m_ws]

theorem rS_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (mEmb k r m *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]

theorem gramProj_mid (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ p, p ∈ P ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧ WithLp.toLp 2 (rW k r p.ofLp) ∈ P₀)
    {n : ℕ} (v : Fin n → Fin (2 * r + k + 1) → ℂ) : gramProj P v = gramProj P₀ fun a => rW k r (v a) := by
  have hin : ∀ x p : EuclideanSpace ℂ (Fin (2 * r + k + 1)), rE k r p.ofLp = 0 → rS k r p.ofLp = 0 →
      ⟪x, p⟫_ℂ = ⟪(WithLp.toLp 2 (rW k r x.ofLp) : EuclideanSpace ℂ _), WithLp.toLp 2 (rW k r p.ofLp)⟫_ℂ := by
    intro x p h1 h2
    have h1' : ∀ a, p.ofLp (eI k r a) = 0 := congrFun h1
    have h2' : ∀ a, p.ofLp (esI k r a) = 0 := congrFun h2
    simp [PiLp.inner_apply, sum3, h1', h2', rW]
  have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
  have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
  have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
  have hpr : ∀ x : Fin (2 * r + k + 1) → ℂ, P.starProjection (WithLp.toLp 2 x) =
      WithLp.toLp 2 (iW k r (P₀.starProjection (WithLp.toLp 2 (rW k r x))).ofLp) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hP]; refine ⟨hE _, hS _, ?_⟩
      simp only [hW]
      exact Submodule.starProjection_apply_mem _ _
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := (hP w).1 hw
      rw [inner_sub_left, hin _ _ h1 h2, hin _ _ h1 h2, ← inner_sub_left]
      simp only [hW]
      exact Submodule.starProjection_inner_eq_zero _ _ h3
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply, hpr]
  rw [hin _ (WithLp.toLp 2 (iW k r _)) (hE _) (hS _)]
  simp only [hW]

theorem gramProj_comb {n : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (T : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → Fin n → ℂ) : gramProj P (fun c => ∑ b, T b c • w b) = ‖T.det‖ * gramProj P w := by
  unfold gramProj
  have : (Matrix.gram ℂ fun c => P.starProjection (WithLp.toLp 2 (∑ b, T b c • w b))) =
      Tᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * T := by
    ext a b
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, WithLp.toLp_sum, WithLp.toLp_smul,
      map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp; ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    mul_right_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg _)]

def Cm (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun b c => (g⁻¹ *ᵥ bvec (eI k r c)) (esI k r b)

section normal
variable {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {β : Fin r → ℕ}

theorem herm_Cm (hn : IsNormal k r β g) (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) w (g⁻¹ *ᵥ bvec (eI k r c)) = ((Cm k r g)ᴴ *ᵥ rE k r w) c := by
  obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 c).1
  rw [herm3, h1, h2]
  simp [herm, Matrix.mulVec, dotProduct, Cm, rS]

theorem fvec_cast (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]
theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem Dmin_r (hn : IsNormal k r β g) : Dmin k r z z' g ⟨r, by omega⟩ = ((Cm k r g)ᴴ).det := by
  unfold Dmin
  congr 1
  ext a b
  show herm (Hpk k r) (g *ᵥ fvec k r z' (Fin.castSucc b)) (fvec k r z (Fin.castSucc a)) = _
  rw [fvec_cast, fvec_cast, ← herm_inv hn.1, herm_Cm hn]
  simp [Matrix.mulVec, dotProduct, rE, bvec_apply, eI_inj]

theorem Dmin_last (hn : IsNormal k r β g) (hz : inWb k r z) : Dmin k r z z' g (Fin.last (r + 1)) =
    herm (Hpk k r) (g *ᵥ z') z * Dmin k r z z' g ⟨r, by omega⟩ := by
  have h1 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h2 : Dmin k r z z' g ⟨r, by omega⟩ = ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  have h3 : ∀ b : Fin r, Zhat k r z z' g (Fin.last r) b.castSucc = 0 := by
    intro b
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 b).2
    obtain ⟨h3, h4⟩ := of_inWb hz
    unfold Zhat
    rw [fvec_cast, fvec_last, herm3, h1, h2, h3]
    simp [herm]
  rw [h1, h2, Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  simp only [h3, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Fin.val_last]
  rw [← two_mul, pow_mul]
  simp [Zhat, fvec_last]

theorem mem_Hcom (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (w : Fin (2 * r + k + 1) → ℂ) :
    w ∈ Hcom k r z z' g ↔ rE k r w = 0 ∧ rS k r w = 0 ∧ herm (Hb k) (rW k r w) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r w) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  show (∀ a : Fin (r + 1), _ ∧ _) ↔ _
  rw [Fin.forall_fin_succ']
  simp only [fvec_cast, fvec_last, herm_e, herm_Cm hn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hS : rS k r w = 0 := funext fun a => (h1 a).1
    have hE : rE k r w = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Cm k r g)ᴴ)
      · rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hC
      · exact funext fun a => (h1 a).2
    rw [herm3, hS, hE] at h2 h3
    exact ⟨hE, hS, by simpa using h2, by simpa using h3⟩
  · rintro ⟨hE, hS, h2, h3⟩
    refine ⟨fun a => ⟨congrFun hS a, by simp [hE]⟩, ?_, ?_⟩ <;> rw [herm3, hS, hE] <;> simpa

theorem mem_sup (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ Hcom k r z z' g ⊔ Xsp k r ↔ rS k r v = 0 ∧ herm (Hb k) (rW k r v) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r v) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, x, hx, rfl⟩
    obtain ⟨-, h2, h3, h4⟩ := (mem_Hcom hn hC w).1 hw
    obtain ⟨h5, h6⟩ := mem_Xsp.1 hx
    have e1 : rW k r (w + x) = rW k r w + rW k r x := rfl
    have e2 : rS k r (w + x) = rS k r w + rS k r x := rfl
    rw [e1, e2, h2, h5, h6, add_zero, add_zero]
    exact ⟨rfl, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
    have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
    have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
    refine ⟨iW k r (rW k r v), (mem_Hcom hn hC _).2 ⟨hE _, hS _, by rwa [hW], by rwa [hW]⟩,
      v - iW k r (rW k r v), mem_Xsp.2 ⟨?_, ?_⟩, by abel⟩
    · show rW k r v - rW k r (iW k r (rW k r v)) = 0
      rw [hW, sub_self]
    · show rS k r v - rS k r (iW k r (rW k r v)) = 0
      rw [hS, h1, sub_self]

theorem Cm_det (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    Dr k r z z' g = ‖(Cm k r g).det‖ ∧ (Cm k r g).det ≠ 0 := by
  have h : Dr k r z z' g = ‖(Cm k r g).det‖ := by
    unfold Dr; rw [Dmin_r hn, Matrix.det_conjTranspose, norm_star]
  exact ⟨h, fun h0 => ht.2.2.2.2.2.2 (by rw [h, h0, norm_zero])⟩

theorem gram_ne (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    herm (Hb k) (rW k r z') (rW k r z') * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) -
      herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r z') ≠ 0 := by
  obtain ⟨hz, hz', -, -, hg, hG, -⟩ := ht
  obtain ⟨z1, z2⟩ := of_inWb hz
  obtain ⟨z1', z2'⟩ := of_inWb hz'
  have hy : rS k r (g⁻¹ *ᵥ z) = 0 := by
    funext a
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 a).2
    show (g⁻¹ *ᵥ z) (esI k r a) = 0
    rw [← herm_e (g⁻¹ *ᵥ z) a, herm_inv' hg, herm3, h1, h2, z1]
    simp [herm]
  have real : ∀ v : Fin (k + 1) → ℂ, herm (Hb k) v v = ((herm (Hb k) v v).re : ℂ) := fun v =>
    (Complex.conj_eq_iff_re.1 (herm_star v v)).symm
  have e1 : herm (Hb k) (rW k r z') (rW k r z') = -(Tz k r z' : ℂ) := by
    rw [real, Tz, herm3, z1', z2']; simp
  have e2 : herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) = -(Tz k r z : ℂ) := by
    have : herm (Hpk k r) z z = herm (Hpk k r) (g⁻¹ *ᵥ z) (g⁻¹ *ᵥ z) := by
      rw [herm_inv hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]
    rw [real, Tz, this, herm3, hy]; simp
  have e3 : herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) = herm (Hpk k r) (g *ᵥ z') z := by
    rw [← herm_inv hg, herm3, z1', z2']; simp
  rw [← herm_star (rW k r z') (rW k r (g⁻¹ *ᵥ z)), e1, e2, e3]
  intro h0
  apply hG
  unfold Gf
  rw [Dmin_last hn hz, map_mul]
  have : Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) = Tz k r z * Tz k r z' := by
    apply Complex.ofReal_injective
    rw [← Complex.mul_conj]
    push_cast
    simp only [Complex.star_def] at h0
    linear_combination -h0
  rw [this, sub_self]

end normal

def pair2 (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] ℂ × ℂ where
  toFun p := (herm (Hb k) (m *ᵥ p.ofLp) s, herm (Hb k) (m *ᵥ p.ofLp) t)
  map_add' p q := by simp [herm, Matrix.mulVec_add]
  map_smul' c p := by simp [herm, Matrix.mulVec_smul]

def Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  LinearMap.ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))

theorem mem_Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ Pz m s t ↔ (herm (Hb k) (m *ᵥ p) s = 0 ∧ herm (Hb k) (m *ᵥ p) t = 0) ∧ p (Fin.last k) = 0 := by
  simp [Pz, pair2]

theorem finrank_Pz {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : IsUnit m.det) {s t : Fin (k + 1) → ℂ}
    (h : herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s ≠ 0) :
    Module.finrank ℂ (Pz m s t) = k - 2 ∨ Module.finrank ℂ (Pz m s t) = k - 1 := by
  have hsurj : LinearMap.range (pair2 m s t) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨x, y⟩
    set D := herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s with hD
    refine ⟨WithLp.toLp 2 (m⁻¹ *ᵥ (((x * herm (Hb k) t t - y * herm (Hb k) t s) / D) • s +
      ((y * herm (Hb k) s s - x * herm (Hb k) s t) / D) • t)), ?_⟩
    have hs : ∀ (c : ℂ) v w, herm (Hb k) (c • v) w = c * herm (Hb k) v w := fun c v w => by
      simp [herm, Matrix.mulVec_smul]
    simp only [pair2, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm,
      Matrix.one_mulVec, herm_add_left, hs, Prod.mk.injEq]
    constructor <;> field_simp <;> rw [hD] <;> ring
  have h1 := LinearMap.finrank_range_add_finrank_ker (pair2 m s t)
  rw [hsurj] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))
  have h3 := Submodule.finrank_le (LinearMap.range ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k))))
  have h4 : Module.finrank ℂ (Pz m s t) ≤ Module.finrank ℂ (LinearMap.ker (pair2 m s t)) := by
    apply Submodule.finrank_mono
    unfold Pz; rw [LinearMap.ker_prod]; exact inf_le_left
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin]
    at h1 h2 h3
  unfold Pz at *
  omega

theorem mem_pos (p : Fin (2 * r + k + 1) → ℂ) : p ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ↔
    rE k r p = rS k r p ∧ rW k r p (Fin.last k) = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    refine ⟨funext fun a => ?_, ?_⟩
    · have := congrFun h (esI k r a); rwa [besselHermForm_mulVec_dualIsotropicIndex] at this
    · have := congrFun h (wI k r (Fin.last k)); rw [H_w] at this
      simp only [sg, if_true] at this
      show p _ = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2⟩
    funext x
    induction x using cases3 with
    | h1 a => rw [H_e]; exact (congrFun h1 a).symm
    | h2 j =>
      rw [H_w]; unfold sg; split_ifs with h
      · subst h; have : p (wI k r (Fin.last k)) = 0 := h2
        simp [this]
      · simp
    | h3 a => rw [besselHermForm_mulVec_dualIsotropicIndex]; exact congrFun h1 a

theorem Yv_normal : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  intro k r z z' g β _ ht hn m hm
  have hmu := unit_of_UH HbHb hm
  obtain ⟨hD, hC⟩ := Cm_det ht hn
  refine ⟨Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)), finrank_Pz hmu (gram_ne ht hn), fun u q a ha => ?_⟩
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.Amp.UEmb.uEmb_hom k r
  set U := upper u with hUdef
  set A : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun b => (a b : ℂ) with hA
  have hUd : U.det = 1 := (hup u).1
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hAu : IsUnit A.det := by
    rw [hA, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  set x := uEmb k r U * pOf k r q * uEmb k r A * mEmb k r m with hx
  have hxu : IsUnit x.det := by
    simp only [hx, Matrix.det_mul]
    exact (((unit_of_UH HH (hU U hUu).1).mul (unit_of_UH HH (pEl_mem_UH _ _ (skewM_skew _ _)))).mul
      (unit_of_UH HH (hU A hAu).1)).mul (unit_of_UH HH (mEmb_mem m hm))
  have xS : ∀ v, rS k r (x *ᵥ v) = (U⁻¹)ᴴ *ᵥ ((A⁻¹)ᴴ *ᵥ rS k r v) := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rS_u, rS_p, rS_m]
  have xW : ∀ v, rW k r (x *ᵥ v) = m *ᵥ rW k r v + ∑ b, ((A⁻¹)ᴴ *ᵥ rS k r v) b • q.1 b := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rW_u, rW_p, rW_m, rS_u, rS_m]
  have hinv : ∀ M : Matrix (Fin r) (Fin r) ℂ, IsUnit M.det → ((M⁻¹)ᴴ).det ≠ 0 := fun M hM => by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (Matrix.isUnit_nonsing_inv_det M hM).ne_zero
  have hP : ∀ p, p ∈ Ppos k r z z' g x ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧
      WithLp.toLp 2 (rW k r p.ofLp) ∈ Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)) := by
    intro p
    show (p.ofLp ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ∧
      Matrix.toLin' x p.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r) ↔ _
    rw [mem_pos, Matrix.toLin'_apply, mem_sup hn hC, mem_Pz, xS, xW]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have h5 := Matrix.eq_zero_of_mulVec_eq_zero (hinv A hAu)
        (Matrix.eq_zero_of_mulVec_eq_zero (hinv U hUu) h3)
      rw [h5] at h4 h1
      exact ⟨h1, h5, by simpa using h4, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rw [h1, h2]
      exact ⟨⟨rfl, h4⟩, by simp, by simpa using h3⟩
  set T : Matrix (Fin r) (Fin r) ℂ := -(Uᴴ * Cm k r g) with hT
  have hv : ∀ c, rW k r (x⁻¹ *ᵥ (g⁻¹ *ᵥ bvec (eI k r c))) = ∑ b, T b c • (m⁻¹ *ᵥ q.1 b) := by
    intro c
    set v := g⁻¹ *ᵥ bvec (eI k r c) with hv
    set y := x⁻¹ *ᵥ v with hy
    have hxy : x *ᵥ y = v := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mulVec]
    have h1 := xS y
    have h2 := xW y
    rw [hxy] at h1 h2
    rw [(of_Xst (hn.2.1 c).1).2] at h2
    have h3 : (A⁻¹)ᴴ *ᵥ rS k r y = Uᴴ *ᵥ rS k r v := by
      rw [h1, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hUu]
      simp
    have h4 : ∀ b, (Uᴴ *ᵥ rS k r v) b = -T b c := fun b => by
      simp [hT, Matrix.mul_apply, Matrix.mulVec, dotProduct, Cm, rS, hv]
    rw [h3] at h2
    have h5 : m *ᵥ rW k r y = ∑ b, T b c • q.1 b := by
      simp only [h4, neg_smul, Finset.sum_neg_distrib] at h2
      exact (eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h2.symm))
    have h6 : rW k r y = m⁻¹ *ᵥ (m *ᵥ rW k r y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hmu, Matrix.one_mulVec]
    rw [h6, h5, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  have hTd : ‖T.det‖ = ‖(Cm k r g).det‖ := by
    rw [hT, Matrix.det_neg, Matrix.det_mul, Matrix.det_conjTranspose, hUd]
    simp
  unfold Yv
  rw [gramProj_mid _ _ hP]
  simp only [hv]
  rw [gramProj_comb, hTd, hD]
  have := norm_ne_zero_iff.2 hC
  field_simp

end GlobalTheory.Amp.NormGram
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  atlas_forward_decl GlobalTheory.Amp.NormGram.Yv_normal
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfOff

lemma exists_blockEnd {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

lemma minor_ne_zero {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

lemma Zr_mul_uEmb {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

lemma N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

theorem offBlock_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dif_neg (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dif_pos hcb, dif_pos hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end GlobalTheory.Amp.NfOff
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offBlock_entries_bounded_normalForm_pairOfFlags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  atlas_forward_decl GlobalTheory.Amp.NfOff.offBlock_le
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RadBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

theorem eucl_comp_le {n N : ℕ} (f : Fin n → Fin N) (hf : Function.Injective f) (v : Fin N → ℂ) :
    eucl (fun j => v (f j)) ≤ eucl v := by
  unfold eucl
  apply Real.sqrt_le_sqrt
  rw [← Finset.sum_image (f := fun i => Complex.normSq (v i)) (fun a _ b _ h => hf h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => Complex.normSq_nonneg _)

theorem eucl_neg {N : ℕ} (v : Fin N → ℂ) : eucl (-v) = eucl v := by
  unfold eucl
  simp [Complex.normSq_neg]

theorem eucl_sum_le {n N : ℕ} (c : Fin n → ℂ) (v : Fin n → Fin N → ℂ) (C R : ℝ) (hc : ∀ a, ‖c a‖ ≤ C)
    (hv : ∀ a, eucl (v a) ≤ R) : eucl (∑ a, c a • v a) ≤ n * (C * R) := by
  have key : eucl (∑ a, c a • v a) ≤ ∑ a, ‖c a‖ * eucl (v a) := by
    rw [eucl_eq]
    have e : (WithLp.toLp 2 (∑ a, c a • v a) : EuclideanSpace ℂ (Fin N)) =
        ∑ a, c a • (WithLp.toLp 2 (v a) : EuclideanSpace ℂ (Fin N)) := by
      ext i
      simp [Finset.sum_apply]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_smul, eucl_eq]
  refine key.trans ?_
  calc ∑ a, ‖c a‖ * eucl (v a) ≤ ∑ _a : Fin n, C * R :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul (hc a) (hv a) (Real.sqrt_nonneg _) ((norm_nonneg _).trans (hc a))
    _ = n * (C * R) := by simp

private theorem hadamard_lemma' {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    ‖A.det‖ ≤ ∏ i, eucl (fun d => A d i) := by
  classical
  let f : Fin j → EuclideanSpace ℂ (Fin j) := fun i => WithLp.toLp 2 (fun d => A d i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin j)) = Fintype.card (Fin j) := by simp
  let B := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  let S := EuclideanSpace.basisFun (Fin j) ℂ
  have hS : S.toBasis.det f = A.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have hmul : S.toBasis.det f = S.toBasis.det B * B.toBasis.det f := by
    have e := AlternatingMap.eq_smul_basis_det B.toBasis S.toBasis.det
    have := congrArg (fun F : EuclideanSpace ℂ (Fin j) [⋀^Fin j]→ₗ[ℂ] ℂ => F f) e
    simpa [OrthonormalBasis.coe_toBasis] using this
  rw [← hS, hmul, norm_mul, S.det_to_matrix_orthonormalBasis B, one_mul,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  calc ‖inner ℂ (B i) (f i)‖ ≤ ‖B i‖ * ‖f i‖ := norm_inner_le_norm _ _
    _ = ‖f i‖ := by rw [B.orthonormal.1 i, one_mul]
    _ = eucl (fun d => A d i) := (eucl_eq _).symm

theorem minor_le {r j : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (f g : Fin j → Fin r) :
    ‖(N.submatrix f g).det‖ ≤ (∏ i, eucl (fun d => (a d : ℂ) * N d (g i))) * ∏ i, (a (f i))⁻¹ := by
  classical
  by_cases hf : Function.Injective f
  · have hA : (N.submatrix f g).det * ∏ i, ((a (f i) : ℂ)) =
        (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)).det := by
      have e : (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) =
          Matrix.diagonal (fun i => (a (f i) : ℂ)) * N.submatrix f g := by
        ext i' i
        simp [Matrix.diagonal_mul]
      rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
    have h1 := hadamard_lemma' (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i))
    rw [← hA, norm_mul, norm_prod] at h1
    have h2 : ∏ i, eucl (fun d => (Matrix.of fun i' i => (a (f i') : ℂ) * N (f i') (g i)) d i) ≤
        ∏ i, eucl (fun d => (a d : ℂ) * N d (g i)) :=
      Finset.prod_le_prod (fun i _ => Real.sqrt_nonneg _)
        (fun i _ => eucl_comp_le f hf (fun d => (a d : ℂ) * N d (g i)))
    have hprod : ∏ i, ‖((a (f i) : ℂ))‖ = ∏ i, a (f i) :=
      Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha _)]
    have hpos : 0 < ∏ i, a (f i) := Finset.prod_pos fun i _ => ha (f i)
    rw [hprod] at h1
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h1.trans h2
  · obtain ⟨i, i', hne, heq⟩ : ∃ i i', i ≠ i' ∧ f i = f i' := by
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨i, i', h, hne⟩ := hf
      exact ⟨i, i', hne, h⟩
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [heq]), norm_zero]
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun i _ => (inv_pos.2 (ha _)).le)

theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc ∏ i, f i ≤ ∏ _i : Fin n, R := Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h i)
    _ = R ^ n := by simp

theorem inv_bound {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b) (R De : ℝ)
    (hR : 1 ≤ R) (hal : ∀ b, (a b)⁻¹ ≤ R) (hN : ∀ b, eucl (fun d => (a d : ℂ) * N d b) ≤ R)
    (hdet : N.det ≠ 0) (hDe : ‖N.det‖⁻¹ ≤ De) :
    (∀ i j, ‖N⁻¹ i j‖ ≤ R ^ (2 * r - 2) * De) ∧ ∀ c, a c ≤ R ^ (2 * r - 1) * De := by
  cases r with
  | zero => exact ⟨fun i => i.elim0, fun c => c.elim0⟩
  | succ n =>
  have hdet0 : 0 < ‖N.det‖ := norm_pos_iff.2 hdet
  have hR0 : 0 ≤ R := by linarith
  have hcol : ∀ b, 0 ≤ eucl (fun d => (a d : ℂ) * N d b) := fun b => Real.sqrt_nonneg _
  have hainv0 : ∀ b, 0 ≤ (a b)⁻¹ := fun b => (inv_pos.2 (ha b)).le
  constructor
  · intro i j
    have hadj : ‖N.adjugate i j‖ ≤ R ^ (2 * (n + 1) - 2) := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
      refine (minor_le N a ha j.succAbove i.succAbove).trans ?_
      have e : 2 * (n + 1) - 2 = n + n := by omega
      rw [e, pow_add]
      exact mul_le_mul (prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _))
        (prod_le_pow' _ R (fun _ => hainv0 _) (fun _ => hal _))
        (Finset.prod_nonneg fun _ _ => hainv0 _) (pow_nonneg hR0 _)
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv, norm_inv, mul_comm]
    exact mul_le_mul hadj hDe (inv_nonneg.2 (norm_nonneg _)) (pow_nonneg hR0 _)
  · intro c
    have h1 := minor_le N a ha (id : Fin (n + 1) → Fin (n + 1)) id
    rw [Matrix.submatrix_id_id] at h1
    have hprodcol : (∏ i, eucl (fun d => (a d : ℂ) * N d (id i))) ≤ R ^ (n + 1) :=
      prod_le_pow' _ R (fun _ => hcol _) (fun _ => hN _)
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (a (id i))⁻¹) (Finset.mem_univ c)] at h1
    have hrest : ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ ≤ R ^ n := by
      calc ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ ≤ ∏ _i ∈ Finset.univ.erase c, R :=
            Finset.prod_le_prod (fun _ _ => hainv0 _) (fun _ _ => hal _)
        _ = R ^ n := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hrest0 : 0 ≤ ∏ i ∈ Finset.univ.erase c, (a (id i))⁻¹ :=
      Finset.prod_nonneg fun _ _ => hainv0 _
    have h2 : ‖N.det‖ ≤ R ^ (n + 1) * ((a c)⁻¹ * R ^ n) :=
      h1.trans (mul_le_mul hprodcol (mul_le_mul_of_nonneg_left hrest (hainv0 c))
        (mul_nonneg (hainv0 c) hrest0) (pow_nonneg hR0 _))
    have hac := ha c
    have e : 2 * (n + 1) - 1 = (n + 1) + n := by omega
    rw [e, pow_add]
    have h3 : a c * ‖N.det‖ ≤ R ^ (n + 1) * R ^ n := by
      calc a c * ‖N.det‖ ≤ a c * (R ^ (n + 1) * ((a c)⁻¹ * R ^ n)) :=
            mul_le_mul_of_nonneg_left h2 hac.le
        _ = R ^ (n + 1) * R ^ n := by field_simp
    calc a c = a c * ‖N.det‖ * ‖N.det‖⁻¹ := by field_simp
      _ ≤ R ^ (n + 1) * R ^ n * De :=
          mul_le_mul h3 hDe (inv_nonneg.2 (norm_nonneg _)) (by positivity)

variable {k r : ℕ}

theorem diag_inv (a : Fin r → ℂ) (ha : ∀ b, a b ≠ 0) :
    (Matrix.diagonal a)⁻¹ = Matrix.diagonal fun b => (a b)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext b
  exact inv_mul_cancel₀ (ha b)

section
open GlobalTheory.Amp.Rad

theorem mE_e (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (mEmb k r m *ᵥ v) (eI k r c) = v (eI k r c) := by
  simp only [Matrix.mulVec, dotProduct, m_e]
  simp

theorem middleSpaceLeviEmbedding_mulVec_dual_isotropic_coord (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (mEmb k r m *ᵥ v) (esI k r c) = v (esI k r c) := by
  simp only [Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]
  simp

theorem mE_w (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (mEmb k r m *ᵥ v) (wI k r j) = (m *ᵥ fun i => v (wI k r i)) j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum3 (k := k) (r := r)]
  simp [m_we, m_ws, m_ww]

theorem uE_e (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (uEmb k r u *ᵥ v) (eI k r c) = ∑ b, u c b * v (eI k r b) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r)]
  simp [UEmb.u_ee, UEmb.u_em, UEmb.u_es]

theorem isotropicLeviEmbedding_mulVec_dual_isotropic_coord (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    (uEmb k r u *ᵥ v) (esI k r c) = ∑ b, star (u⁻¹ b c) * v (esI k r b) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r)]
  simp [UEmb.u_se, UEmb.u_sm, UEmb.u_ss]

theorem uE_w (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (uEmb k r u *ᵥ v) (wI k r j) = v (wI k r j) := by
  have hw : wI k r j = UEmb.mI k r j := Fin.ext rfl
  simp only [Matrix.mulVec, dotProduct]
  rw [UEmb.sum_idx (k := k) (r := r), hw]
  simp [UEmb.u_me, UEmb.u_mm, UEmb.u_ms]

theorem col_comp (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) (d : Fin r) :
    (∀ c, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (esI k r c) = if c = d then (a c : ℂ) else 0) ∧
    (∀ j, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (wI k r j) = -(m⁻¹ *ᵥ B d) j) ∧
    (∀ c, ((pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r d))
      (eI k r c) = (a c : ℂ)⁻¹ * (-S c d - herm (Hb k) (B d) (B c) / 2)) := by
  have ha0 : ∀ b, (a b : ℂ) ≠ 0 := fun b => by exact_mod_cast (ha b).ne'
  have hD : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)
  have hinv : (pEl k r B S * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ =
      mEmb k r m⁻¹ * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) * pEl k r (-B) (-S)) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mEmb_inv m hm, UEmb.uEmb_inv _ hD, pEl_inv,
      diag_inv _ ha0]
  have hv : ∀ x, (pEl k r (-B) (-S) *ᵥ bvec (esI k r d)) x = pEl k r (-B) (-S) x (esI k r d) :=
    fun x => mulVec_bvec _ _ _
  have hDi : (Matrix.diagonal fun b => (a b : ℂ)⁻¹)⁻¹ = Matrix.diagonal fun b => (a b : ℂ) := by
    rw [diag_inv _ (fun b => inv_ne_zero (ha0 b))]
    simp
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨fun c => ?_, fun j => ?_, fun c => ?_⟩
  · rw [middleSpaceLeviEmbedding_mulVec_dual_isotropic_coord, isotropicLeviEmbedding_mulVec_dual_isotropic_coord, hDi]
    simp [Matrix.diagonal_apply, hv, pEl_ss]
    by_cases h : c = d
    · subst h
      simp [Complex.conj_ofReal]
    · simp [h, Ne.symm h]
  · rw [mE_w]
    have e : (fun i => (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹) *ᵥ
        (pEl k r (-B) (-S) *ᵥ bvec (esI k r d))) (wI k r i)) = -B d := by
      funext i
      rw [uE_w, hv, pEl_ws]
      rfl
    rw [e, Matrix.mulVec_neg]
    rfl
  · rw [mE_e, uE_e]
    simp [Matrix.diagonal_apply, hv, pEl_es, herm_neg_left, herm_neg_right]

theorem Xst_eq {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xst k r) :
    v = ∑ c, v (esI k r c) • bvec (esI k r c) := by
  unfold Xst at hv
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  have hw : ∀ c, (∑ i, w i • bvec (esI k r i)) (esI k r c) = w c := by
    intro c
    simp [Finset.sum_apply, bvec_apply, esI_inj]
  simp_rw [hw]

theorem dr_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dmin k r z z' g ⟨r, by omega⟩ = (Zr k r g).det := by
  unfold Dmin
  congr 1
  ext a b
  simp [Zhat, Zr, fvec, NfMid.herm_e, mulVec_bvec]

end

theorem radical_coords_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  intro k r z z' g₀ β De R₀ hTF hNorm hDeOK hR₀ m hm y q a ha hSz' hSz
  classical
  have UH_mul : ∀ {g h : Mat k r}, g ∈ UH (Hpk k r) → h ∈ UH (Hpk k r) → g * h ∈ UH (Hpk k r) := by
    intro g h hg hh
    simp only [UH, Set.mem_setOf_eq] at hg hh ⊢
    rw [Matrix.conjTranspose_mul,
      show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by simp only [Matrix.mul_assoc],
      hg, hh]
  have uEmb_Xst : ∀ (V : Matrix (Fin r) (Fin r) ℂ) {w : Fin (2 * r + k + 1) → ℂ},
      w ∈ Xst k r → uEmb k r V *ᵥ w ∈ Xst k r := by
    intro V w hw
    rw [Xst_eq hw, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Matrix.mulVec_smul, UEmb.uEmb_esI]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨a, rfl⟩
  have skew_le : ∀ (S K : Matrix (Fin r) (Fin r) ℂ), (∀ c d, star (S d c) = -S c d) →
      (∀ c d, star (K d c) = K c d) → ∀ T : ℝ, (∀ c d, ‖S c d + K c d‖ ≤ T) →
      ∀ c d, ‖S c d‖ ≤ T := by
    intro S K hS hK T h c d
    have e : S c d = ((S c d + K c d) - star (S d c + K d c)) / 2 := by
      rw [star_add, hS, hK]
      ring
    have h1 := norm_sub_le (S c d + K c d) (star (S d c + K d c))
    rw [norm_star] at h1
    rw [e, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [h c d, h d c]
  obtain ⟨hzW, hz'W, -, -, hg₀, -, hDr⟩ := hTF
  obtain ⟨x, hxdef⟩ : ∃ x, x = uEmb k r (upperOff β y) * pOf k r q *
      uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = pEl k r q.1 (skewM q.2.1 q.2.2) *
      uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m := ⟨_, rfl⟩
  rw [← hxdef] at hSz' hSz
  have hR0 : 0 ≤ R₀ := by linarith
  have hDe0 : 0 ≤ De := by linarith [hDeOK.1]
  have ha0 : ∀ b, (a b : ℂ) ≠ 0 := fun b => by exact_mod_cast (ha b).ne'
  have hDu : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b _ => ha0 b)
  have hUdet : (upperOff β y).det = 1 := UEmb.det_upper _
  have hUu : IsUnit (upperOff β y).det := by rw [hUdet]; exact isUnit_one
  have hSskew : (skewM q.2.1 q.2.2)ᴴ = -skewM q.2.1 q.2.2 := Rad.skewM_skew _ _
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := UEmb.upper_mem _
  have hPN : pEl k r q.1 (skewM q.2.1 q.2.2) ∈ Nset k r :=
    (((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 hSskew).1
  have hDG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := UEmb.uEmb_mem _ hDu
  have hMG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hDMG := UH_mul hDG hMG
  have hQG : Q ∈ GG k r := by rw [hQ]; exact UH_mul (UH_mul hPN.1 hDG) hMG
  have hxQ : x = uEmb k r (upperOff β y) * Q := by
    rw [hxdef, hQ, pOf]
    simp only [Matrix.mul_assoc]
  have hxG : x ∈ GG k r := by rw [hxQ]; exact UH_mul hUN.1 hQG
  have hx'G : g₀ * x ∈ GG k r := UH_mul hg₀ hxG
  have h1UW : ∀ w : Fin (2 * r + k + 1) → ℂ, (1 : Mat k r) ∈ UWset k r w := by
    intro w
    simp [UWset, UH]
  have hSset : ∀ w, ∀ n ∈ Nset k r, n ∈ Sset k r w :=
    fun w n hn => ⟨1, h1UW w, n, hn, (one_mul n).symm⟩
  have h1K : (1 : Mat k r) ∈
      (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨by simp [UH], Submonoid.one_mem _⟩
  have LB' := LInv.lengths_basic k r z' hz'W
  have LB := LInv.lengths_basic k r z hzW
  have hal : ∀ b, (a b)⁻¹ ≤ R₀ := by
    intro b
    have e1 := (LB'.1 Q hQG _ (hSset z' _ hUN) 1 h1K).1 b.castSucc
    have e2 := (LB'.1 _ hDMG _ (hSset z' _ hPN) 1 h1K).1 b.castSucc
    have e3 := LB'.2.1 a ha m hm b
    have hQ' : Q = pEl k r q.1 (skewM q.2.1 q.2.2) *
        (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) * 1 := by
      rw [hQ, Matrix.mul_one, Matrix.mul_assoc]
    calc (a b)⁻¹ = lA k r z' x b.castSucc := by
          rw [hxQ, ← Matrix.mul_one (uEmb k r (upperOff β y) * Q), e1, hQ', e2, e3]
      _ ≤ Sg k r z' x := ((LB'.2.2 x).2.1 _).2
      _ ≤ R₀ := hSz'
  obtain ⟨u', hu'len, -⟩ := GramFlag.gramSchmidt_lengths k r z (g₀ * x) hx'G
  have hWb : ∀ a', eucl (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ R₀ := by
    intro a'
    rw [(hu'len a').1]
    exact ((LB.2.2 (g₀ * x)).2.1 _).2.trans hSz
  obtain ⟨Mm, hMm⟩ : ∃ Mm : Matrix (Fin r) (Fin r) ℂ, Mm = (upperOff β y)ᴴ * Zr k r g₀⁻¹ :=
    ⟨_, rfl⟩
  have hM : ∀ b, (g₀ * x)⁻¹ *ᵥ bvec (eI k r b) = ∑ d, Mm d b • (Q⁻¹ *ᵥ bvec (esI k r d)) := by
    intro b
    have hyX : uEmb k r (upperOff β y)⁻¹ *ᵥ (g₀⁻¹ *ᵥ bvec (eI k r b)) ∈ Xst k r :=
      uEmb_Xst _ (hNorm.2.1 b).1
    rw [hxQ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, UEmb.uEmb_inv _ hUu, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Xst_eq hyX, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mulVec_smul]
    congr 1
    rw [isotropicLeviEmbedding_mulVec_dual_isotropic_coord, Matrix.nonsing_inv_nonsing_inv _ hUu, hMm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.conjTranspose_apply, Rad.mulVec_bvec]
    rfl
  obtain ⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin r) (Fin r) ℂ, Nm = Mm * upper u' := ⟨_, rfl⟩
  have hW' : ∀ a', (∑ b, upper u' b a' • ((g₀ * x)⁻¹ *ᵥ bvec (eI k r b))) =
      ∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d)) := by
    intro a'
    simp_rw [hM, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, hNm, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hWb' : ∀ a', eucl (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) ≤ R₀ := by
    intro a'
    rw [← hW' a']
    exact hWb a'
  have hcol := fun d => col_comp q.1 (skewM q.2.1 q.2.2) a ha m hm d
  simp only [← hQ] at hcol
  have hcol1 : ∀ d c, (Q⁻¹ *ᵥ bvec (esI k r d)) (esI k r c) = if c = d then (a c : ℂ) else 0 :=
    fun d => (hcol d).1
  have hNcol : ∀ a', eucl (fun c => (a c : ℂ) * Nm c a') ≤ R₀ := by
    intro a'
    have e : (fun c => (a c : ℂ) * Nm c a') =
        fun c => (∑ d, Nm d a' • (Q⁻¹ *ᵥ bvec (esI k r d))) (esI k r c) := by
      funext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol1]
      simp [mul_comm]
    rw [e]
    exact (eucl_comp_le (esI k r) (fun c c' h => (Rad.esI_inj c c').1 h) _).trans (hWb' a')
  have hZr : Zr k r g₀⁻¹ = (Zr k r g₀)ᴴ := NfMid.zr_inv hg₀
  have hdr := dr_eq z z' g₀
  have hZne : ‖(Zr k r g₀).det‖ ≠ 0 := by rw [← hdr]; exact hDr
  have hZDe : ‖(Zr k r g₀).det‖⁻¹ ≤ De := by
    rw [← hdr]
    exact hDeOK.2 ⟨r, by omega⟩ le_rfl (by rw [hdr]; exact norm_ne_zero_iff.1 hZne)
  have hdetN : ‖Nm.det‖ = ‖(Zr k r g₀).det‖ := by
    rw [hNm, Matrix.det_mul, hMm, Matrix.det_mul, hZr, Matrix.det_conjTranspose,
      Matrix.det_conjTranspose, hUdet, UEmb.det_upper]
    simp
  have hNdet : Nm.det ≠ 0 := by
    intro h
    apply hZne
    rw [← hdetN, h, norm_zero]
  have hNDe : ‖Nm.det‖⁻¹ ≤ De := by rw [hdetN]; exact hZDe
  obtain ⟨hinvE, hac⟩ := inv_bound Nm a ha R₀ De hR₀ hal hNcol hNdet hNDe
  have hNu : Nm * Nm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNdet)
  have hErep : ∀ d, Q⁻¹ *ᵥ bvec (esI k r d) =
      ∑ a', Nm⁻¹ a' d • ∑ d', Nm d' a' • (Q⁻¹ *ᵥ bvec (esI k r d')) := by
    intro d
    funext i
    have hone := fun d' => congrFun (congrFun hNu d') d
    simp only [Matrix.mul_apply] at hone
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc (Q⁻¹ *ᵥ bvec (esI k r d)) i
        = ∑ d', (1 : Matrix (Fin r) (Fin r) ℂ) d' d * (Q⁻¹ *ᵥ bvec (esI k r d')) i := by
          simp [Matrix.one_apply]
      _ = _ := by
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [← hone d', Finset.sum_mul]
          exact Finset.sum_congr rfl fun a' _ => by ring
  have hEbd : ∀ d, eucl (Q⁻¹ *ᵥ bvec (esI k r d)) ≤ r * R₀ ^ (2 * r - 1) * De := by
    intro d
    have hr : 1 ≤ r := by have := d.isLt; omega
    rw [hErep d]
    refine (eucl_sum_le (fun a' => Nm⁻¹ a' d) _ (R₀ ^ (2 * r - 2) * De) R₀
      (fun a' => hinvE a' d) hWb').trans (le_of_eq ?_)
    have e : 2 * r - 1 = (2 * r - 2) + 1 := by omega
    rw [e, pow_succ]
    ring
  have hSK : ∀ c d, ‖skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2‖ ≤
      r * R₀ ^ (4 * r - 2) * De ^ 2 := by
    intro c d
    have hr : 1 ≤ r := by have := d.isLt; omega
    have e1 := (hcol d).2.2 c
    have e2 : skewM q.2.1 q.2.2 c d + herm (Hb k) (q.1 d) (q.1 c) / 2 =
        -((a c : ℂ) * (Q⁻¹ *ᵥ bvec (esI k r d)) (eI k r c)) := by
      rw [e1, ← mul_assoc, mul_inv_cancel₀ (ha0 c), one_mul]
      ring
    rw [e2, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha c)]
    calc a c * ‖(Q⁻¹ *ᵥ bvec (esI k r d)) (eI k r c)‖
        ≤ (R₀ ^ (2 * r - 1) * De) * (r * R₀ ^ (2 * r - 1) * De) :=
          mul_le_mul (hac c) ((LInv.norm_le_eucl _ _).trans (hEbd d)) (norm_nonneg _)
            (mul_nonneg (pow_nonneg hR0 _) hDe0)
      _ = r * R₀ ^ (4 * r - 2) * De ^ 2 := by
          have e : 4 * r - 2 = (2 * r - 1) + (2 * r - 1) := by omega
          rw [e, pow_add]
          ring
  have hskew : ∀ c d : Fin r, ‖skewM q.2.1 q.2.2 c d‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
    intro c d
    refine skew_le (skewM q.2.1 q.2.2) (Matrix.of fun c d => herm (Hb k) (q.1 d) (q.1 c) / 2)
      (fun c d => ?_) (fun c d => ?_) _ (fun c d => ?_) c d
    · have := congrFun (congrFun hSskew c) d
      simpa [Matrix.conjTranspose_apply] using this
    · simp only [Matrix.of_apply]
      rw [div_eq_mul_inv, div_eq_mul_inv, star_mul', Rad.herm_star]
      simp
    · simpa only [Matrix.of_apply] using hSK c d
  refine ⟨fun b => ?_, fun p => ?_, fun b => ?_⟩
  · have e : m⁻¹ *ᵥ q.1 b = -(fun j => (Q⁻¹ *ᵥ bvec (esI k r b)) (wI k r j)) := by
      funext j
      simp only [Pi.neg_apply, (hcol b).2.1 j, neg_neg]
    rw [e, eucl_neg]
    exact (eucl_comp_le (wI k r) (fun j j' h => (Rad.wI_inj j j').1 h) _).trans (hEbd b)
  · have e : q.2.1 p = skewM q.2.1 q.2.2 p.1.1 p.1.2 := by
      simp only [skewM, dif_pos p.2]
    rw [e]
    exact hskew _ _
  · have e : skewM q.2.1 q.2.2 b b = (q.2.2 b : ℂ) * Complex.I := by
      simp [skewM]
    have := hskew b b
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
    exact this

end GlobalTheory.Amp.RadBound
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_coordinates_bounded_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → (∀ b, eucl (m⁻¹ *ᵥ q.1 b) ≤ r * R₀ ^ (2 * r - 1) * De) ∧ (∀ p, ‖q.2.1 p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2) ∧ ∀ b, |q.2.2 b| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by
  atlas_forward_decl GlobalTheory.Amp.RadBound.radical_coords_le
end

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem vol_gram_codim_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  intro k j _ hjk m hm P hP0
  have hP : k - 2 ≤ Module.finrank ℂ P := by omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : d + 2 - 2 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 3 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 2 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (measure_mono fun B hB => ?_)
      (le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_))
    · exact ⟨hB.1, hB.2.2⟩
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have h2 : M ^ (2 * j ^ 2) ≤ 4 * M ^ (2 * j ^ 2 + 2 * j) := by
      have h3 : M ^ (2 * j ^ 2) ≤ M ^ (2 * j ^ 2 + 2 * j) := pow_le_pow_right₀ hM (Nat.le_add_right _ _)
      have h4 : 0 ≤ M ^ (2 * j ^ 2 + 2 * j) := by positivity
      linarith
    calc _ = (Real.pi * M ^ 2) ^ (3 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (3 * j) * (4 * M ^ (2 * j ^ 2 + 2 * j)) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = _ := by
          rw [← pow_mul (Real.exp 1 / s), mul_comm s j, ← mul_pow, mul_div_assoc, mul_assoc _ (4 : ℝ)]

end GlobalTheory.Amp.GramVol
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_gramCondition_codim_two_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  atlas_forward_decl GlobalTheory.Amp.GramVol.vol_gram_codim_three
end

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem volume_product_le : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  intro r R₀ De hr hR hD
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hm : 2 * ((s + 1) * (s + 1 - 1) / 2) ≤ (s + 1) * s := by
    rw [Nat.add_sub_cancel]; omega
  generalize (s + 1) * (s + 1 - 1) / 2 = m at hm ⊢
  have e1 : 4 * (s + 1) - 2 = 4 * s + 2 := by omega
  have e2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e1, e2]
  have hx : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hr
  generalize ((s + 1 : ℕ) : ℝ) = x at hx ⊢
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have h24 : (2 : ℝ) ≤ 4 := by norm_num
  have hms : 2 * m * s ≤ (s + 1) * s * s := Nat.mul_le_mul_right s hm
  calc _ ≤ ((4 : ℝ) * (R₀ ^ (2 * (s + 1)) * De) ^ 2) ^ m * ((4 * (x * R₀ ^ (4 * s + 2) * De ^ 2) ^ 2) ^ m * (4 * (x * R₀ ^ (4 * s + 2) * De ^ 2)) ^ (s + 1)) * ((4 * (x * R₀ ^ (2 * s + 1) * De) ^ 2) ^ (3 * (s + 1)) * 4 * (x * R₀ ^ (2 * s + 1) * De) ^ (2 * (s + 1) ^ 2 + 2 * (s + 1)) * 4 ^ ((s + 1) ^ 2)) := by
        gcongr
    _ = (4 : ℝ) ^ (2 * m + (s + 1) + 3 * (s + 1) + 1 + (s + 1) ^ 2) *
          x ^ (2 * m + (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          R₀ ^ (4 * (s + 1) * m + (4 * s + 2) * 2 * m + (4 * s + 2) * (s + 1) + (2 * s + 1) * 2 * (3 * (s + 1)) + (2 * s + 1) * (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          De ^ (6 * m + 2 * (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) := by
        simp only [mul_pow, ← pow_mul]
        generalize (4 : ℝ) = c
        ring
    _ ≤ (4 : ℝ) ^ (11 * (s + 1) ^ 2) * x ^ (11 * (s + 1) ^ 2) * R₀ ^ (20 * (s + 1) ^ 3) * De ^ (12 * (s + 1) ^ 2) := by
        have h4 : (1 : ℝ) ≤ 4 := by norm_num
        gcongr
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s), Nat.zero_le (s * s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
    _ = _ := by rw [mul_pow]

end GlobalTheory.Amp
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  atlas_forward_decl GlobalTheory.Amp.volume_product_le
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibNf

theorem card_UT (r : ℕ) : Fintype.card (UT r) = r * (r - 1) / 2 := by
  rw [Fintype.card_subtype, ← Nat.choose_two_right]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
  simpa using this

theorem vol_polydisc (ι : Type) [Fintype ι] {R : ℝ} (hR : 0 ≤ R) :
    volume {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = ENNReal.ofReal ((Real.pi * R ^ 2) ^ Fintype.card ι) := by
  have h : {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem vol_cube (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = ENNReal.ofReal ((2 * R) ^ r) := by
  have h : {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem sfinite_PPar (k r : ℕ) : SFinite (volume : Measure (PPar k r)) := by
  have : SFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  have : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := inferInstance
  infer_instance

theorem vol_PPar (k r : ℕ) (S : Set (Fin r → Fin (k + 1) → ℂ)) (T : Set (UT r → ℂ)) (U : Set (Fin r → ℝ)) :
    (volume : Measure (PPar k r)) (S ×ˢ (T ×ˢ U)) = volume S * (volume T * volume U) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]

theorem coords_upper {r : ℕ} (u : UT r → ℂ) : USplit.coords (upper u) = u := by
  funext p
  exact USplit.upper_of_lt u p.2

theorem measurable_coord (k r : ℕ) : Measurable fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) :=
  (show Continuous fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) from (NCoord.coord_homeo k r).2.1).measurable

theorem coord_mem (k r : ℕ) (u : UT r → ℂ) (q : PPar k r) : uEmb k r (upper u) * pOf k r q ∈ Nset k r := by
  have := (NCoord.coord_homeo k r).1.mapsTo (Set.mem_univ (u, q))
  simpa only using this

theorem coord_off_mem (k r : ℕ) (β : Fin r → ℕ) (y : UToff β → ℂ) (q : PPar k r) :
    uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := by
  unfold upperOff
  exact coord_mem k r _ q

theorem cut_le {k r : ℕ} {β : Fin r → ℕ} (φ : Mt k r → ℝ≥0∞) (hφ : SubCut (Nset k r) (lebR k r β) φ)
    (n : Mat k r) (hN : n ∈ Nset k r) :
    ∫⁻ x : UTin β → ℂ, φ (Matrix.of.symm (uEmb k r (upperIn β x) * n)) ≤ 1 := by
  have h1 := hφ.2 (Matrix.of.symm n) hN
  have hl : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (Matrix.of.symm n : Mt k r)) :=
    hφ.1.comp (continuous_rmulM n).measurable
  have hi : Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
      unfold upperIn
      refine (NCoord.cont_uEmb k r).comp (continuous_pi fun p => ?_)
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
    exact Continuous.measurable (γ := Mt k r) this
  unfold lebR at h1
  rw [lintegral_map hl hi] at h1
  exact h1

theorem lintegral_le {k r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (φ : Mt k r → ℝ≥0∞)
    (hφ : SubCut (Nset k r) (lebR k r β) φ) (E : Set (Mt k r)) (hE : MeasurableSet E)
    (A : Set (UToff β → ℂ)) (B : Set (PPar k r))
    (h : ∀ x y q, (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ∈ E →
      y ∈ A ∧ q ∈ B) :
    ∫⁻ n, φ n * E.indicator 1 n ∂(lebN k r) ≤ volume A * volume B := by
  have hm : Measurable fun n => φ n * E.indicator 1 n := hφ.1.mul (measurable_one.indicator hE)
  have hF := measurable_coord k r
  have := sfinite_PPar k r
  unfold lebN
  rw [lintegral_map hm hF, Measure.volume_eq_prod]
  refine le_trans (lintegral_prod_symm' _ (hm.comp hF)).le ?_
  refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_const_le B (volume A))
  have hc : Measurable fun U : Fin r → Fin r → ℂ => USplit.coords (Matrix.of U) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)
  have hs := (USplit.lebesgue_split r β hβ).2 _ ((hm.comp hF).comp (hc.prodMk (measurable_const (a := q))))
  simp only [Function.comp_apply, Equiv.apply_symm_apply, coords_upper] at hs
  have hp : ∀ x y, uEmb k r (upper (USplit.coords (upperIn β x * upperOff β y))) * pOf k r q =
      uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q) := by
    intro x y
    have : upper (USplit.coords (upperIn β x * upperOff β y)) = upperIn β x * upperOff β y :=
      USplit.upper_coords_mul _ _
    rw [this, UEmb.uEmb_mul, Matrix.mul_assoc]
  simp only [hp] at hs
  simp only [Function.comp_apply]
  rw [hs]
  have key : ∀ y, ∫⁻ x : UTin β → ℂ,
      φ (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q))) *
        E.indicator 1 (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ≤
      A.indicator (fun _ => B.indicator 1 q) y := by
    intro y
    by_cases hy : y ∈ A ∧ q ∈ B
    · rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hy.2]
      refine le_trans (lintegral_mono fun x => ?_) (cut_le φ hφ _ (coord_off_mem k r β y q))
      exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le) _)
    · refine le_trans (le_of_eq ?_) zero_le
      have : ∀ x : UTin β → ℂ, E.indicator (1 : Mt k r → ℝ≥0∞)
          (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) = 0 :=
        fun x => Set.indicator_of_notMem (fun hx => hy (h x y q hx)) _
      simp only [this, mul_zero, lintegral_zero]
  refine le_trans (lintegral_mono key) (le_trans (lintegral_indicator_const_le A _) (le_of_eq ?_))
  by_cases hq : q ∈ B <;> simp [hq]

theorem arith {a b c d e f g : ℝ} (hpos : 0 ≤ e * f) (har : a * (b * c) * d ≤ g) :
    a * (d * e * f * (b * c)) ≤ g * e * f := by
  have := mul_le_mul_of_nonneg_right har hpos
  refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_)) <;> ring

theorem null_of {k r : ℕ} (Z : Set (Mt k r)) (hZ : MeasurableSet Z) (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S = 0)
    (h : ∀ u q, (Matrix.of.symm (uEmb k r (upper u) * pOf k r q) : Mt k r) ∈ Z → q.1 ∈ S) : lebN k r Z = 0 := by
  have := sfinite_PPar k r
  unfold lebN
  rw [Measure.map_apply (measurable_coord k r) hZ]
  refine measure_mono_null (t := Set.univ ×ˢ (S ×ˢ (Set.univ ×ˢ Set.univ))) (fun q hq => ?_) ?_
  · exact ⟨trivial, h q.1 q.2 hq, trivial, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod, vol_PPar, hS, zero_mul, mul_zero]

theorem mem_of_mul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ ρ x : Mat k r} {R₀ y : ℝ}
    (hz : inWb k r z) (hz' : inWb k r z') (hg : g₀ ∈ GG k r) (hρ : ρ ∈ Rset k r g₀) (hx0 : x ∈ GG k r)
    (hx : (Matrix.of.symm (ρ * x) : Mt k r) ∈ Eset k r z z' g₀ R₀ y) :
    Sg k r z' x ≤ R₀ ∧ Sg k r z (g₀ * x) ≤ R₀ ∧ y < Yv k r z z' g₀ x ∧ Yv k r z z' g₀ x ≤ 2 * y := by
  have hx' : Sg k r z' (ρ * x) ≤ R₀ ∧ Sg k r z (g₀ * (ρ * x)) ≤ R₀ ∧ y < Yv k r z z' g₀ (ρ * x) ∧
      Yv k r z z' g₀ (ρ * x) ≤ 2 * y := hx.2
  have h1 : (1 : Mat k r) ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨(nSubgroup k r).1.1, one_mem _⟩
  have e1 := ((LInv.lengths_basic k r z' hz').1 _ hx0 _ (YInv.N_sub_S z' hρ.1) 1 h1).2
  have e2 := ((LInv.lengths_basic k r z hz).1 _ (YInv.mul_mem hg hx0) _ (YInv.N_sub_S z hρ.2) 1 h1).2
  have e3 := (YInv.yv_invariant k r z z' g₀ hz hz' hg _ hx0).2.2 _ hρ
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_assoc _ g₀⁻¹, ← Matrix.mul_assoc g₀⁻¹, Matrix.nonsing_inv_mul _ (YInv.det_unit hg),
    Matrix.one_mul, Matrix.mul_assoc g₀] at e2
  rwa [e1, e2, e3] at hx'

theorem vol_bound {k r : ℕ} (β : Fin r → ℕ) {R₀ De y : ℝ} (hr : 1 ≤ r) (hR : 1 ≤ R₀) (h1De : 1 ≤ De) (hy : 0 < y)
    (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S ≤ ENNReal.ofReal ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 *
      (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) *
      (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r)))) :
    volume {y : UToff β → ℂ | ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De} *
      (volume : Measure (PPar k r)) (S ×ˢ ({s : UT r → ℂ | ∀ p, ‖s p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2} ×ˢ
          {t : Fin r → ℝ | ∀ p, |t p| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2})) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  have hR1 : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) h1De
  have hR3 : 0 ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by positivity
  rw [vol_PPar, vol_polydisc _ (zero_le_one.trans hR1), vol_polydisc _ hR3, vol_cube _ hR3, card_UT]
  have hcard : Fintype.card (UToff β) ≤ r * (r - 1) / 2 := card_UT r ▸ Fintype.card_subtype_le _
  have hb : 1 ≤ Real.pi * (R₀ ^ (2 * r) * De) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) (one_le_pow₀ hR1)
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hb hcard))
    (mul_le_mul' hS le_rfl)) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have har := GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower r R₀ De hr hR h1De
  have hpos : 0 ≤ (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    (2 * y) ^ (2 * (k - 2 - r)) := by positivity
  unfold fibVol
  exact arith hpos har

theorem fibre_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  intro k r z z' g₀ β De hr hk hT hN hD m hm a ha
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection k r z z' g₀ β (by omega) hT hN m hm
  obtain ⟨hV0, hV⟩ := GlobalTheory.T.volume_gramCondition_codim_two_three k r hr hk m hm P₀ hP₀
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' g₀ hN.1
  have hU := fun R₀ hR => GlobalTheory.T.offBlock_entries_bounded_normalForm_pairOfFlags k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hB := fun R₀ hR => GlobalTheory.T.radical_coordinates_bounded_majorant_lengths k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hdG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := by
    apply UEmb.uEmb_mem
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  have hmG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hNq := coord_mem k r
  have hY' := fun u q => hY u q a ha
  have hU' := fun R₀ hR w q => hU R₀ hR w q a ha
  have hB' := fun R₀ hR w q => hB R₀ hR w q a ha
  have hcG := YInv.mul_mem hdG hmG
  simp only [Matrix.mul_assoc _ (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)))] at hY' hU' hB'
  clear hY hU hB
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = c at *
  have hrm : Measurable (rmulM c) := (continuous_rmulM c).measurable
  constructor
  · have hZ : MeasurableSet ((Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
        (fun x => Yv k r z z' g₀ (Matrix.of x)) ∘ rmulM c) ⁻¹' {0}) := (hM1.comp hrm) (measurableSet_singleton 0)
    refine measure_mono_null (fun n hn => ?_) (null_of _ hZ _ hV0 fun u q hq => ?_)
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    · have := Set.indicator_apply_eq_zero.1 hq (YInv.mul_mem (hNq u q).1 hcG)
      exact (hY' u q).symm.trans this
  · intro φ hφ R₀ y hR hy
    have h1De : 1 ≤ De := hD.1
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hR2 : 1 ≤ r * R₀ ^ (2 * r - 1) * De :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr' (one_le_pow₀ hR)) h1De
    refine le_trans ?_ (vol_bound β hr hR h1De hy _ (hV _ y hR2 hy))
    refine le_trans (le_of_eq ?_) (lintegral_le hN.2.2.1 φ hφ (rmulM c ⁻¹' Eset k r z z' g₀ R₀ y) (hrm (hM2 R₀ y)) _ _ ?_)
    · refine lintegral_congr fun n => ?_
      congr 1
    · intro x w q hx
      have hρ : uEmb k r (upperIn β x) ∈ Rset k r g₀ := by
        rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r g₀ β hN).1]; exact ⟨x, rfl⟩
      have hn0 : uEmb k r (upperOff β w) * pOf k r q ∈ Nset k r := coord_off_mem k r β w q
      have hx0 : uEmb k r (upperOff β w) * pOf k r q * c ∈ GG k r := YInv.mul_mem hn0.1 hcG
      have hx1 : (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β w) * pOf k r q * c)) : Mt k r) ∈
          Eset k r z z' g₀ R₀ y := by
        rw [← Matrix.mul_assoc]; exact hx
      obtain ⟨s1, s2, s3, s4⟩ := mem_of_mul hT.1 hT.2.1 hN.1 hρ hx0 hx1
      have e4 : Yv k r z z' g₀ (uEmb k r (upperOff β w) * pOf k r q * c) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
        unfold upperOff
        exact hY' _ q
      rw [e4] at s3 s4
      obtain ⟨b1, b2, b3⟩ := hB' R₀ hR w q s1 s2
      exact ⟨hU' R₀ hR w q s1 s2, ⟨b1, s3, s4⟩, b2, b3⟩

end GlobalTheory.Amp.FibNf
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  atlas_forward_decl GlobalTheory.Amp.FibNf.fibre_bound
end
