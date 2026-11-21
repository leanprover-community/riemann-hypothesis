import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadingBlockLowerEntriesToBlockCoords
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPhlaBound
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

section
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

noncomputable section

theorem lintegral_exp_muF_eq_setLIntegral_Om (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 =
      ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  have hT : Measurable (GlobalTheory.UpCoordCompare.toEntries X) :=
    (GlobalTheory.UpCoordCompare.contDiff_toEntries X).continuous.measurable
  have hf : Measurable fun z => ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((GlobalTheory.PoleDbar.measurable_rhF X x0.1).const_mul s).neg)
  have hd : Measurable fun z => ENNReal.ofReal (density X x0 z) := by
    have e : (fun z => ENNReal.ofReal (density X x0 z)) =
        (fun z => ENNReal.ofReal (densF X x0.1 z)) ∘ GlobalTheory.UpCoordCompare.toEntries X := by
      funext z
      simp only [Function.comp_apply, GlobalTheory.UpCoordCompare.densF_toEntries]
    rw [e]
    exact (OntoC.measurable_densF X x0.1).comp hT
  have hOm : MeasurableSet (Om X) := by
    have : Om X = GlobalTheory.UpCoordCompare.toEntries X ⁻¹' OmF X x0.1 := by
      ext z; exact (GlobalTheory.UpCoordCompare.toEntries_mem_OmF_iff X x0 z).symm
    rw [this]
    exact hT (ExF.isOpen_OmF X x0.1).measurableSet
  rw [← GlobalTheory.UpCoordCompare.map_mu X x0, lintegral_map hf hT, mu,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hOm fun z hz => ?_
  simp only [Pi.mul_apply, GlobalTheory.UpCoordCompare.rhF_toEntries X x0 hz]

end

end GlobalTheory.IntBall
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 = ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  atlas_forward_decl GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder

theorem norm_det_le_add_rankOne {k : ℕ} (P : Matrix (Fin k) (Fin k) ℂ) (hP : P.PosSemidef)
    (v : Fin k → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖P.det‖ ≤ ‖(P + (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))).det‖ := by
  by_cases hu : IsUnit P.det
  · have hPD : P.PosDef := hP.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 hu)
    have hinv : (P⁻¹).PosSemidef := hPD.inv.posSemidef
    have e : (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v)) =
        replicateCol (Fin 1) ((c : ℂ) • v) * replicateRow (Fin 1) (star v) := by
      ext i j; simp [Matrix.mul_apply, mul_assoc]
    have h1 : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + replicateRow (Fin 1) (star v) * P⁻¹ *
        replicateCol (Fin 1) ((c : ℂ) • v)).det = 1 + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v) := by
      rw [Matrix.det_fin_one]
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      rw [Finset.sum_comm]
    rw [e]
    erw [det_add_replicateCol_mul_replicateRow (ι := Fin 1) hu]
    rw [norm_mul]
    erw [h1]
    have hre : 0 ≤ (star v ⬝ᵥ P⁻¹ *ᵥ v).re := by
      have := hinv.re_dotProduct_nonneg v
      simpa using this
    have h2 : 1 ≤ ‖(1 : ℂ) + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith
    have h3 : 0 ≤ ‖P.det‖ := norm_nonneg _
    nlinarith
  · have : P.det = 0 := by simpa using hu
    rw [this, norm_zero]; exact norm_nonneg _

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder

theorem schur_bound {m k : ℕ} (Z : Matrix (Fin m) (Fin 1) ℂ) (N : Matrix (Fin m) (Fin k) ℂ)
    (hd : 0 < (1 - Zᴴ * Z).det.re) :
    (1 - Zᴴ * Z).det.re * ‖(Nᴴ * N).det‖ ≤
      ‖((fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N).det‖ := by
  set d : Matrix (Fin 1) (Fin 1) ℂ := 1 - Zᴴ * Z with hdd
  have hprod : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N =
      fromBlocks d (-(Zᴴ * N)) (-(Nᴴ * Z)) (-(Nᴴ * N)) := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hdd, sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg]
  have hdet : d.det = d 0 0 := Matrix.det_fin_one d
  have hherm : d.IsHermitian := Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)
  have him : (d 0 0).im = 0 := by
    have := hherm.apply 0 0
    have h2 : (starRingEnd ℂ) (d 0 0) = d 0 0 := this
    exact Complex.conj_eq_iff_im.1 h2
  set δ : ℝ := d.det.re with hδ
  have hreal : d.det = (δ : ℂ) := by
    apply Complex.ext
    · simp [hδ]
    · simp [hdet, him]
  have hne : d.det ≠ 0 := by
    rw [hreal]; exact_mod_cast hd.ne'
  haveI : Invertible d := Matrix.invertibleOfIsUnitDet d (isUnit_iff_ne_zero.2 hne)
  have hinvd : ⅟d = (((δ : ℂ))⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.inv_def, Matrix.adjugate_fin_one, hreal]
    rw [← hdet, hreal]
  rw [hprod, det_fromBlocks₁₁]
  set v : Fin k → ℂ := fun j => (Nᴴ * Z) j 0 with hv
  have hs : ∀ j, (Zᴴ * N) 0 j = star (v j) := by
    intro j
    simp only [hv, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hcr : Nᴴ * Z * (Zᴴ * N) = replicateCol (Fin 1) v * replicateRow (Fin 1) (star v) := by
    ext i j
    rw [Matrix.mul_apply (M := Nᴴ * Z), Fin.sum_univ_one, hs j, Matrix.mul_apply (M := replicateCol (Fin 1) v),
      Fin.sum_univ_one]
    rfl
  have hrk : -(Nᴴ * N) - -(Nᴴ * Z) * ⅟d * -(Zᴴ * N) =
      -((Nᴴ * N) + ((δ⁻¹ : ℝ) : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))) := by
    rw [hinvd, ← hcr]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    push_cast
    module
  rw [hrk, Matrix.det_neg, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hreal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  gcongr
  exact norm_det_le_add_rankOne _ (Matrix.posSemidef_conjTranspose_mul_self N) v _
    (inv_nonneg.2 hd.le)

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lowMat_diag (w : Low r → ℂ) (a : Fin r) : lowMat w a a = 1 := by
  simp [lowMat]

theorem lowMat_upper (w : Low r → ℂ) {a b : Fin r} (h : a < b) : lowMat w a b = 0 := by
  have h1 : ¬ b < a := fun h' => lt_asymm h h'
  have h2 : a ≠ b := ne_of_lt h
  simp [lowMat, h1, h2]

theorem mat_nFrame (X : Data E r) (hp : X.p0 = 1) (z : V (nd X)) (τ : X.Ψ) :
    mat (nFrame X z) τ = lowMat (zOf X z τ) := by
  rw [← nmat_eq_lowMat]
  ext a b
  show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = nmat X z τ a b
  simp only [zFrame, leviFrame, hp]
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have n00 : ∀ c : Fin r, nmat X z τ c c = 1 := fun c => by simp [nmat]
  have nup : ∀ c d : Fin r, c < d → nmat X z τ c d = 0 := fun c d h => by
    have h1 : ¬ d < c := fun h' => lt_asymm h h'
    have h2 : c ≠ d := ne_of_lt h
    simp [nmat, h1, h2]
  by_cases hb : (b : ℕ) < 1
  · have hb0 : b = ⟨0, hr⟩ := Fin.ext (by simp; omega)
    subst hb0
    rw [Finset.sum_eq_single ⟨0, hr⟩]
    · by_cases ha : 1 ≤ (a : ℕ)
      · simp [ha, n00]
      · have ha0 : a = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        subst ha0; simp [n00]
    · intro c _ hc
      have hc1 : 1 ≤ (c : ℕ) := by
        by_contra h; apply hc; exact Fin.ext (by simp; omega)
      simp [hc1]
    · simp
  · rw [Finset.sum_eq_single a]
    · have : ¬ (1 ≤ (a : ℕ) ∧ (a : ℕ) < 1) := by omega
      simp [this, hb]
      intro h1 h2; omega
    · intro c _ hca
      by_cases hc : (c : ℕ) < 1
      · have h1 : c < b := Fin.lt_def.2 (by omega)
        simp [hb, nup c b h1]
      · have : ¬ (1 ≤ (a : ℕ) ∧ (c : ℕ) < 1) := by omega
        simp [this, Ne.symm hca]
        intro _ _ h3; omega
    · simp

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_transpose (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose, gram_eq_transpose, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

def eR (r : ℕ) (hr : 1 ≤ r) : Fin 1 ⊕ Fin (r - 1) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

def eC (k : ℕ) : Fin 1 ⊕ Fin k ≃ Fin (k + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem eR_inl (hr : 1 ≤ r) (i : Fin 1) : ((eR r hr (Sum.inl i) : Fin r) : ℕ) = i := by
  simp [eR]

@[simp] theorem eR_inr (hr : 1 ≤ r) (i : Fin (r - 1)) : ((eR r hr (Sum.inr i) : Fin r) : ℕ) = 1 + i := by
  simp [eR]

@[simp] theorem eC_inl (k : ℕ) (i : Fin 1) : ((eC k (Sum.inl i) : Fin (k + 1)) : ℕ) = i := by
  simp [eC]

@[simp] theorem eC_inr (k : ℕ) (i : Fin k) : ((eC k (Sum.inr i) : Fin (k + 1)) : ℕ) = 1 + i := by
  simp [eC]; omega

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne

theorem zDet_mul_colGram_le_norm_dmin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 = 1 →
    ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)),
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.castSucc ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hp x0 z hz τ k
  have hr : 1 ≤ r := by have := k.isLt; omega
  have hk : (k : ℕ) + 1 ≤ r := by have := k.isLt; omega
  set w := zOf X z τ with hw
  set L : Matrix (Fin r) (Fin r) ℂ := lowMat w with hL
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
  have hgram : gram τ.1 X.Gm (mat (point X x0 z) τ) = Lᵀ * D * L.map (starRingEnd ℂ) := by
    have : mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ := rfl
    rw [this, gram_mul_right, x0.2 τ, mat_nFrame X hp]
  set f : Fin 1 ⊕ Fin k → Fin r := fun j => Fin.castLE hk (eC k j) with hf
  set A : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin k) ℂ := L.submatrix (eR r hr) f with hA
  set D' : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin (r - 1)) ℂ := D.submatrix (eR r hr) (eR r hr) with hD'
  have hdmin : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ = (Aᵀ * D' * A.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [hgram, ← Matrix.det_submatrix_equiv_self (eC k), Matrix.submatrix_submatrix]
    congr 1
    rw [Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective,
      Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective, hA, hD', Matrix.transpose_submatrix,
      Matrix.submatrix_map]
    rfl
  set Zm : Matrix (Fin (r - 1)) (Fin 1) ℂ := fun i _ => A (Sum.inr i) (Sum.inl 0) with hZm
  set Nm : Matrix (Fin (r - 1)) (Fin k) ℂ := fun i j => A (Sum.inr i) (Sum.inr j) with hNm
  have hAb : A = Matrix.fromBlocks 1 0 Zm Nm := by
    ext (i | i) (j | j)
    · have h : eR r hr (Sum.inl i) = f (Sum.inl j) := Fin.ext (by simp [hf, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j])
      simp only [Matrix.fromBlocks_apply₁₁, hA, Matrix.submatrix_apply]
      rw [h, hL, lowMat_diag, Subsingleton.elim i j, Matrix.one_apply_eq]
    · have h : eR r hr (Sum.inl i) < f (Sum.inr j) := Fin.lt_def.2 (by simp [hf, Fin.fin_one_eq_zero i])
      simp only [Matrix.fromBlocks_apply₁₂, hA, Matrix.submatrix_apply, Matrix.zero_apply]
      rw [hL, lowMat_upper w h]
    · rw [Fin.fin_one_eq_zero j]; rfl
    · rfl
  have hDb : D' = Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;>
      simp [hD', hD, Matrix.diagonal_apply, sgn, hp, Matrix.one_apply, (eR r hr).injective.eq_iff] <;>
      split_ifs <;> simp
  have hT : Aᵀ * D' * A.map (starRingEnd ℂ) = (Aᴴ * D' * A)ᵀ := by
    have h1 : D'ᵀ = D' := by rw [hDb, Matrix.fromBlocks_transpose]; simp
    have h2 : (Aᴴ)ᵀ = A.map (starRingEnd ℂ) := by ext i j; simp
    rw [Matrix.transpose_mul, Matrix.transpose_mul, h1, h2, Matrix.mul_assoc]
  have hzD : zDet X z τ = (1 - Zmᴴ * Zm).det.re := by
    unfold zDet
    haveI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by show 0 < X.p0; omega⟩
        uniq := fun b => Subtype.ext (Fin.ext (by
          have h1 : ((b : Fin r) : ℕ) < X.p0 := b.2
          show ((b : Fin r) : ℕ) = 0
          omega)) }
    rw [Matrix.det_unique, Matrix.det_fin_one]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hmem : ∀ i : Fin (r - 1), X.p0 ≤ (i : ℕ) + 1 := fun i => by omega
    let eqv : Fin (r - 1) ≃ {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { toFun := fun i => ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩
        invFun := fun a => ⟨(a.1 : ℕ) - 1, by have := a.1.2; omega⟩
        left_inv := fun i => Fin.ext (by simp)
        right_inv := fun a => Subtype.ext (Fin.ext (by
          have h1 : X.p0 ≤ ((a : Fin r) : ℕ) := a.2
          show ((a : Fin r) : ℕ) - 1 + 1 = (a : Fin r)
          omega)) }
    have key : ∀ i : Fin (r - 1), Zm i 0 = zBlock X z τ ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩ default := by
      intro i
      simp only [hZm, hA, Matrix.submatrix_apply, hL, zBlock, Matrix.of_apply]
      rw [← congrFun (congrFun (nmat_eq_lowMat X z τ) _) _, Matrix.of_apply]
      congr 1
      · exact Fin.ext (by simp; omega)
      · have h1 : (((default : {b : Fin r // (b : ℕ) < X.p0}) : Fin r) : ℕ) < X.p0 :=
          (default : {b : Fin r // (b : ℕ) < X.p0}).2
        exact Fin.ext (by simp [hf]; omega)
    congr 2
    exact (Fintype.sum_equiv eqv _ _ fun i => by rw [key i]; rfl).symm
  have hcG : colGram (blkW X.p0 (zOf X z τ)) k.castSucc = ‖(Nmᴴ * Nm).det‖ := by
    unfold colGram lminor
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.conjTranspose_submatrix]
    have hN : (blkW X.p0 (zOf X z τ)).submatrix id (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc k).isLt)) = Nm := by
      ext i j
      simp only [Matrix.submatrix_apply, blkW, hp, if_true, hNm, hA, hL, id]
      congr 1
      · exact Fin.ext (by simp; omega)
      · exact Fin.ext (by simp [hf]; omega)
    rw [hN]
  rw [hdmin, hT, Matrix.det_transpose, hzD, hcG, hAb, hDb]
  apply schur_bound
  rw [← hzD]
  exact zDet_pos X hz τ

end GlobalTheory.IntBallMinorOne
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 = 1 → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.castSucc ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  atlas_forward_decl GlobalTheory.IntBallMinorOne.zDet_mul_colGram_le_norm_dmin
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.MinorLast

open Matrix
open scoped ComplexOrder

theorem det_sub_bound {p m : ℕ} (N : Matrix (Fin p) (Fin m) ℂ) (q : Fin p → ℂ) :
    (1 - ∑ c, ‖q c‖ ^ 2) * ‖(Nᴴ * N).det‖ ≤
      ‖(Nᴴ * N - vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det‖ := by
  set A := Nᴴ * N with hAdef
  set u := q ᵥ* N with hu
  by_cases hA : A.det = 0
  · rw [hA]; simp
  have hU : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hsplit : A - vecMulVec (star u) u = A + replicateCol Unit (-star u) * replicateRow Unit u := by
    ext i j
    simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply, sub_eq_add_neg]
  have key : (A - vecMulVec (star u) u).det = A.det * (1 - u ⬝ᵥ A⁻¹ *ᵥ star u) := by
    rw [hsplit, Matrix.det_add_mul _ _ hU]
    congr 1
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, sub_eq_add_neg,
      Finset.mul_sum]
    simp only [Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  set P := N * A⁻¹ * Nᴴ with hPdef
  have hs : u ⬝ᵥ A⁻¹ *ᵥ star u = q ⬝ᵥ P *ᵥ star q := by
    rw [hu, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hAh : Aᴴ = A := by rw [hAdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hAh, Matrix.mul_assoc]
  have hPP : P * P = P := by
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hU
    calc P * P = N * (A⁻¹ * (Nᴴ * N) * A⁻¹) * Nᴴ := by simp only [hPdef, Matrix.mul_assoc]
      _ = P := by rw [← hAdef, h1, Matrix.one_mul, hPdef, Matrix.mul_assoc]
  have hQ : (1 - P) = (1 - P)ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hPP]
    simp
  have hpsd : (1 - P).PosSemidef := by rw [hQ]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have ht := hpsd.dotProduct_mulVec_nonneg (star q)
  rw [star_star, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at ht
  have hqq : q ⬝ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_sum,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have ha := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  rw [← hAdef] at ha
  rw [key, hs]
  set a := A.det
  set t := q ⬝ᵥ star q - q ⬝ᵥ P *ᵥ star q with htdef
  have hsq : q ⬝ᵥ P *ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - t := by rw [htdef, hqq]; ring
  rw [hsq]
  obtain ⟨ha1, ha2⟩ := Complex.nonneg_iff.1 ha
  obtain ⟨ht1, ht2⟩ := Complex.nonneg_iff.1 ht
  have hae : a = (a.re : ℂ) := Complex.ext rfl (by simp [← ha2])
  have hte : t = (t.re : ℂ) := Complex.ext rfl (by simp [← ht2])
  rw [hae, hte, Complex.norm_real, Real.norm_of_nonneg ha1]
  rw [show (a.re : ℂ) * (1 - (((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - (t.re : ℂ))) = ((a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real]
  calc (1 - ∑ c, ‖q c‖ ^ 2) * a.re ≤ a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) := by nlinarith
    _ ≤ _ := Real.le_norm_self _

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (x * y) = yᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ G x * y.map (starRingEnd ℂ) := by
  rw [gram_eq_mul, gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem entry_tdm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ) (i j : Fin r) :
    (Mᵀ * Matrix.diagonal d * M.map (starRingEnd ℂ)) i j = ∑ l, M l i * d l * starRingEnd ℂ (M l j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

variable {p : ℕ} (X : Data E (p + 1))

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) (a b : Fin (p + 1)) :
    nmat X z τ a b = lowMat (zOf X z τ) a b := rfl

theorem n_top (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (i a : Fin p) :
    mat (nFrame X z) τ i.castSucc a.castSucc = lowMat (zOf X z τ) i.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ i.castSucc c * leviFrame X z τ c a.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hl : zFrame X z τ i.castSucc (Fin.last p) = 0 := by
    simp [zFrame, hp, Fin.ext_iff]; omega
  rw [hl, zero_mul, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [zFrame, leviFrame, hp, nmat_eq]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro b _ hb
    have : i.castSucc ≠ b.castSucc := fun h => hb (Fin.castSucc_injective _ h).symm
    simp [zFrame, hp, this]
  · simp

theorem n_last (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (a : Fin p) :
    mat (nFrame X z) τ (Fin.last p) a.castSucc =
      ∑ c : Fin p, lowMat (zOf X z τ) (Fin.last p) c.castSucc * lowMat (zOf X z τ) c.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ (Fin.last p) c * leviFrame X z τ c a.castSucc) = _
  simp [zFrame, leviFrame, hp, nmat_eq, Fin.sum_univ_castSucc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_neg (by omega)]

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card (X : Data E (p + 1)) (hp : X.p0 = p) (x0 : Base X) (z : V (nd X)) (τ : X.Ψ)
    (k : Fin p) :
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  set w := zOf X z τ with hw
  let N : Matrix (Fin p) (Fin ((k : ℕ) + 1)) ℂ := fun i a => lowMat w i.castSucc (Fin.castSucc ⟨a, by omega⟩)
  let q : Fin p → ℂ := fun c => lowMat w (Fin.last p) c.castSucc
  have hA : colGram (blkW X.p0 w) k.succ = ‖(Nᴴ * N).det‖ := by
    have hB : blkW X.p0 w = fun (i j : Fin (p + 1 - 1)) => lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      funext i j
      unfold blkW
      split_ifs with h
      · have hi : (i : ℕ) = 0 := by omega
        have hj : (j : ℕ) = 0 := by omega
        simp [lowMat, hi, hj, Fin.ext_iff]
      · rfl
    rw [hB]
    rfl
  have hZ : zDet X z τ = 1 - ∑ c, ‖q c‖ ^ 2 := by
    unfold zDet
    rw [Matrix.det_one_sub_mul_comm]
    letI hU : Unique {a : Fin (p + 1) // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨Fin.last p, by simp [hp]⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp; omega)) }
    rw [Matrix.det_unique]
    let e : Fin p ≃ {b : Fin (p + 1) // (b : ℕ) < X.p0} :=
      { toFun := fun c => ⟨c.castSucc, by simp [hp]⟩
        invFun := fun b => ⟨b.1, by have := b.2; omega⟩
        left_inv := fun c => rfl
        right_inv := fun b => rfl }
    have hs : ∑ b : {b : Fin (p + 1) // (b : ℕ) < X.p0},
        zBlock X z τ default b * star (zBlock X z τ default b) = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Fintype.sum_equiv e (fun c => zBlock X z τ default (e c) * star (zBlock X z τ default (e c)))
        _ (fun _ => rfl)]
      push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      change q c * star (q c) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hs]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hD : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ =
      (Nᴴ * N - Matrix.vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det := by
    have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (point X x0 z) τ) =
        (mat (nFrame X z) τ)ᵀ * Matrix.diagonal (fun a : Fin (p + 1) => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          (mat (nFrame X z) τ).map (starRingEnd ℂ) := by
      rw [show mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ from rfl, gram_mul, x0.2 τ]
    unfold dmin lminor
    rw [hg, ← Matrix.det_transpose (Nᴴ * N - _)]
    congr 1
    ext a b
    have hc : ∀ a : Fin ((k : ℕ) + 1), (Fin.castLE (by omega) a : Fin (p + 1)) =
        Fin.castSucc (⟨a, by omega⟩ : Fin p) := fun a => Fin.ext rfl
    rw [Matrix.submatrix_apply, hc, hc, entry_tdm, Fin.sum_univ_castSucc]
    simp only [n_top X hp, n_last X hp, Fin.val_castSucc, Fin.val_last, sgn, hp, Fin.is_lt, if_true,
      lt_irrefl, if_false, Matrix.transpose_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply, N, q, ← hw]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_one, Complex.ofReal_neg,
      mul_one, Complex.star_def]
    rw [sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · ring
  rw [hA, hZ, hD]
  exact det_sub_bound N q

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

theorem zDet_mul_colGram_le_dmin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hr x0 z _ τ k
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨X.p0, hr.symm⟩
  exact finiteRing_sq_sub_mul_sq_eq_of_card X (by omega) x0 z τ k

end GlobalTheory.IntBall.MinorLast
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  atlas_forward_decl GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.ColGramPos

open scoped ComplexOrder

theorem blkW_upper {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i j : Fin (r - 1)) (h : i < j) :
    blkW p0 w i j = 0 := by
  have h' : (i : ℕ) < j := h
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
  · unfold lowMat
    rw [dif_neg (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]

theorem blkW_diag {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  · unfold lowMat
    rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem lowerTri_det_one {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by
  rw [Matrix.det_of_lowerTriangular T (fun i j hij => hu i j hij)]
  simp [hd]

theorem colGram_blkW_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  intro r p0 w k
  set B := blkW p0 w with hB
  have hk : (k : ℕ) ≤ r - 1 := Nat.le_of_lt_succ k.isLt
  set N : Matrix (Fin (r - 1)) (Fin k) ℂ := B.submatrix id (Fin.castLE hk) with hN
  have hsub : (Bᴴ * B).submatrix (Fin.castLE hk) (Fin.castLE hk) = Nᴴ * N := by
    ext a b
    simp [N, Matrix.mul_apply, Matrix.conjTranspose_apply]
  set T : Matrix (Fin k) (Fin k) ℂ := B.submatrix (Fin.castLE hk) (Fin.castLE hk) with hT
  have hTdet : T.det = 1 := by
    apply lowerTri_det_one
    · intro i j hij
      exact blkW_upper p0 w _ _ (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    · intro i
      exact blkW_diag p0 w _
  have hinj : Function.Injective N.mulVec := by
    intro u v huv
    have h0 : N *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have hT0 : T *ᵥ (u - v) = 0 := by
      ext i
      have := congrFun h0 (Fin.castLE hk i)
      simpa [T, N, Matrix.mulVec, dotProduct] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hTdet]; exact one_ne_zero) hT0
    exact sub_eq_zero.mp this
  have hpd : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hinj
  have hdet : (Nᴴ * N).det ≠ 0 := hpd.det_pos.ne'
  unfold colGram lminor
  rw [hsub]
  exact norm_pos_iff.mpr hdet

end GlobalTheory.IntBall.ColGramPos
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  atlas_forward_decl GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem blkW_det_eq_one (r p0 : ℕ) (w : Low r → ℂ) : (blkW p0 w).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [blkW, lowMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [blkW, lowMat]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)

theorem colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  unfold colGram lminor
  have : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r - 1)).isLt) : Fin (r - 1) → Fin (r - 1)) = id := by
    funext i; ext; simp
  rw [this, Matrix.submatrix_id_id, Matrix.det_mul, Matrix.det_conjTranspose, blkW_det_eq_one]
  simp

theorem colGramLast : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last

end GlobalTheory.IntBall
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  atlas_forward_decl GlobalTheory.IntBall.colGramLast
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.DetLe

theorem re_det_one_sub_le_of_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Unique ι]
    (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.sub_re, Complex.one_re, Complex.re_sum]
  have : ∀ a : κ, 0 ≤ (star (Z a default) * Z a default).re := by
    intro a
    rw [show star (Z a default) = (starRingEnd ℂ) (Z a default) from rfl, mul_comm, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  linarith [Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => this a]

theorem re_det_one_sub_le_of_unique' {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_one_sub_mul_comm]
  have := re_det_one_sub_le_of_unique (Zᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

end GlobalTheory.IntBall.DetLe

namespace GlobalTheory.IntBall

open GlobalTheory.IntBall.DetLe

theorem zDet_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  intro E _ _ _ r X h z _ τ
  have hle := X.p0_le
  unfold zDet
  rcases h with h | h
  · letI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by simp [h]⟩
        uniq := fun b => Subtype.ext (Fin.ext (by have := b.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique _
  · letI : Unique {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨⟨X.p0, by omega⟩, le_refl _⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique' _

end GlobalTheory.IntBall
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  atlas_forward_decl GlobalTheory.IntBall.zDet_le_one
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Cutoff

noncomputable section

theorem norm_entry_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℂ) (a : m) (b : n) :
    ‖Z a b‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ := by
  set v : EuclideanSpace ℂ n := EuclideanSpace.single b (1 : ℂ)
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at h1
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin Z v) a
  have h3 : (Matrix.toEuclideanLin Z v) a = Z a b := by
    simp [v, Matrix.toEuclideanLin_apply, Matrix.mulVec_single]
  rw [h3] at h2
  exact h2.trans h1

theorem gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w :=
  Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)

theorem ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  intro E _ _ _ r X z hz
  rw [bnd, ENNReal.ofReal_prod_of_nonneg (fun τ _ => gB_nonneg _ _)]
  refine le_of_eq (Finset.prod_congr rfl fun τ _ => ?_)
  rw [hB, Set.indicator_of_mem (zOf_mem_cut X hz τ)]

end

end GlobalTheory.IntBall.Cutoff
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  atlas_forward_decl GlobalTheory.IntBall.Cutoff.ofReal_bnd_le
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

noncomputable section

theorem measurePreserving_curry_lowCoord (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem lintegral_prod_zOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  intro E _ _ _ r X h hh
  set e := Fintype.equivFin (Ent X) with he
  set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)
  have s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm
  set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK
  have hKm : Measurable K := Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)
  have s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) := by
    refine ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans
      (lintegral_congr fun f => ?_)
    simp only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g :=
    (measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm
  rw [s1, s2, s3, hK, volume_pi]
  exact GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable

end

end GlobalTheory.IntBall
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  atlas_forward_decl GlobalTheory.IntBall.lintegral_prod_zOf
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem measurable_hB : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  intro r p0
  have hlow : Continuous (fun w : Low r → ℂ => lowMat w) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [lowMat]
    split_ifs <;> first | exact continuous_apply _ | exact continuous_const
  have hblk : Continuous (fun w : Low r → ℂ => blkW p0 w) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hent : ∀ a b : Fin r, Continuous (fun w : Low r → ℂ => lowMat w a b) := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp hlow)
    by_cases h : p0 = 1
    · simp only [blkW, h, if_true]
      exact hent _ _
    · simp only [blkW, h, if_false]
      exact hent _ _
  have hcg : ∀ k, Continuous (fun w : Low r → ℂ => colGram (blkW p0 w) k) := by
    intro k
    simp only [colGram, lminor]
    exact (((hblk.matrix_conjTranspose.matrix_mul hblk).matrix_submatrix _ _).matrix_det).norm
  have hg : Measurable (fun w : Low r → ℂ => gB p0 w) := by
    have hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
      rw [zpow_neg]; norm_cast
    simp only [gB, hz]
    refine Finset.measurable_prod _ fun k _ => ?_
    exact ((hcg k.castSucc).measurable.pow_const 2).inv
  have hS : IsClosed {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply p).norm continuous_const
  unfold hB
  exact (ENNReal.measurable_ofReal.comp hg).indicator hS.measurableSet

end GlobalTheory.IntBall
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  atlas_forward_decl GlobalTheory.IntBall.measurable_hB
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  atlas_forward_decl GlobalTheory.IntBall.lintegral_hB_one_two_lt_top
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin3

theorem norm_one_add_conj_mul (z : ℂ) : ‖1 + (starRingEnd ℂ) z * z‖ = 1 + ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_of_nonneg (by positivity)]

theorem gB_one (w : Low 3 → ℂ) : gB 1 w = (1 + ‖w ⟨(2, 1), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

theorem gB_two (w : Low 3 → ℂ) : gB 2 w = (1 + ‖w ⟨(1, 0), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

noncomputable def dom (x : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) 1).indicator 1 x + ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))

theorem measurable_dom : Measurable dom := by
  unfold dom
  refine Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem lintegral_dom_lt_top : ∫⁻ x, dom x < ⊤ := by
  unfold dom
  rw [lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    exact measure_closedBall_lt_top
  · exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top

theorem le_prod_dom (w : Low 3 → ℂ) (e : Low 3) (hw : ∀ p, p ≠ e → ‖w p‖ ≤ 1) :
    ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) ≤ ∏ p, dom (w p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  calc ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) = ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) * 1 :=
        (mul_one _).symm
    _ ≤ dom (w e) * ∏ p ∈ Finset.univ.erase e, dom (w p) := by
      refine mul_le_mul' ?_ ?_
      · unfold dom
        refine le_trans (le_of_eq ?_) le_add_self
        congr 1
        rw [show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      · refine Finset.one_le_prod' fun p hp => ?_
        unfold dom
        refine le_trans (le_of_eq ?_) le_self_add
        rw [Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]
        rfl

theorem hB_le (p0 : ℕ) (hp : p0 = 1 ∨ p0 = 2) (w : Low 3 → ℂ) : hB p0 w ≤ ∏ p, dom (w p) := by
  unfold hB
  by_cases hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
  · rw [Set.indicator_of_mem hS]
    rcases hp with rfl | rfl
    · rw [gB_one]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
    · rw [gB_two]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
  · rw [Set.indicator_of_notMem hS]
    exact bot_le

theorem lintegral_hB_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  intro p0 hp
  refine lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_
  have h := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ)
    (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)
  rw [volume_pi, h]
  exact ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top

end GlobalTheory.IntBall.Fin3
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  atlas_forward_decl GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem colGram_three_unitLower : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  intro M hd hu
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h01 : M 0 1 = 0 := hu 0 1 (by decide)
  have h02 : M 0 2 = 0 := hu 0 2 (by decide)
  have h12 : M 1 2 = 0 := hu 1 2 (by decide)
  have e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  have e2 : lminor (Mᴴ * M) 2 =
      (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0 := by
    unfold lminor
    exact Matrix.det_fin_two _
  have g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have g2 : lminor (Mᴴ * M) 2 =
      ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      <;> ring
  have pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · unfold colGram
    rw [g1, add_assoc, pos _ (by positivity), ← add_assoc]
  · unfold colGram
    rw [g2, add_assoc, pos _ (by positivity), ← add_assoc]

end GlobalTheory.IntBall
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLower_three : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.IntBall.colGram_three_unitLower
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.FlagGram

theorem cube_cbrt (t : ℝ) (ht : 0 ≤ t) : (t ^ (1/3:ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem rpow_neg_four_thirds (t : ℝ) (ht : 0 ≤ t) :
    t ^ (-(4/3:ℝ)) = ((t ^ (1/3:ℝ)) ^ 4)⁻¹ := by
  rw [Real.rpow_neg ht, ← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem sq_mul_le_cubes (a w : ℝ) (ha : 1 ≤ a) (hw : 1 ≤ w) :
    a ^ 2 * w ≤ a ^ 3 + w ^ 3 - 1 := by
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  rcases le_total a w with h | h
  · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ w) (sub_nonneg.2 h)) (by linarith : (0:ℝ) ≤ w + a)]
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h)]

theorem key (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hBD : B ≤ D) :
    ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤
      (1 + A) ^ (-(4 / 3 : ℝ)) * (1 + C) ^ (-(4 / 3 : ℝ)) *
        ((1 + B) ^ (-(4 / 3 : ℝ)) + (1 + D) ^ (-(4 / 3 : ℝ))) := by
  rw [rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith),
    rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith)]
  have eA := cube_cbrt (1 + A) (by linarith)
  have eB := cube_cbrt (1 + B) (by linarith)
  have eC := cube_cbrt (1 + C) (by linarith)
  have hα : 1 ≤ (1 + A) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hβ : 1 ≤ (1 + B) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hγ : 1 ≤ (1 + C) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hδ : 0 < (1 + D) ^ (1/3:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  generalize (1 + A) ^ (1/3:ℝ) = α at *
  generalize (1 + B) ^ (1/3:ℝ) = β at *
  generalize (1 + C) ^ (1/3:ℝ) = γ at *
  generalize (1 + D) ^ (1/3:ℝ) = δ at *
  have hx : α ^ 2 * β ≤ 1 + A + B := by have := sq_mul_le_cubes α β hα hβ; linarith
  have hy : γ ^ 2 * β ≤ 1 + C + D := by have := sq_mul_le_cubes γ β hγ hβ; linarith
  have hp1 : 0 < α ^ 2 * β := by positivity
  have hp2 : 0 < γ ^ 2 * β := by positivity
  have hprod : (α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2 ≤ (1 + A + B) ^ 2 * (1 + C + D) ^ 2 := by
    gcongr
  have hδ4 : 0 < (δ ^ 4)⁻¹ := by positivity
  calc ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤ ((α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hprod
    _ = (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * (β ^ 4)⁻¹ := by
        rw [← mul_inv, ← mul_inv]; congr 1; ring
    _ ≤ (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * ((β ^ 4)⁻¹ + (δ ^ 4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end GlobalTheory.FlagGram

namespace GlobalTheory

theorem flagGram_density_ineq : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  intro a b c
  rcases le_total (‖b‖ ^ 2) (‖a * c - b‖ ^ 2) with h | h
  · exact FlagGram.key _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) h
  · have := FlagGram.key (‖c‖ ^ 2) (‖a * c - b‖ ^ 2) (‖a‖ ^ 2) (‖b‖ ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity) h
    calc _ = ((1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2 * (1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2)⁻¹ := by
          rw [mul_comm]
      _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGram_density_inequality_complex : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  atlas_forward_decl GlobalTheory.flagGram_density_ineq
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory

theorem lintegral_update_sub_shear {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → ℂ) → ℂ) (hg : Measurable g)
    (hgi : ∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v)
    (F : (ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ i) with he
  have he_mp : MeasurePreserving e := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) _

  set c : ({j // j ≠ i} → ℂ) → ℂ := fun x => g (e.symm (x, 0)) with hc
  have hcm : Measurable c :=
    hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  set S : ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) → ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) :=
    fun p => (p.1, p.2 + (fun _ => - c p.1)) with hS
  have hS_mp : MeasurePreserving S (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun x y => y + (fun _ => - c x))
      (MeasurePreserving.id volume) ?_ ?_
    · exact measurable_snd.add (measurable_pi_lambda _ fun _ => (hcm.comp measurable_fst).neg)
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _
  have hT : (fun w => Function.update w i (w i - g w)) = e.symm ∘ S ∘ e := by
    funext w
    have hgw : g w = c (e w).1 := by
      apply hgi
      intro j hj
      simp [hc, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hgw, sub_eq_add_neg]
    · simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  have hmp : MeasurePreserving (e.symm ∘ S ∘ e) :=
    he_mp.symm.comp (hS_mp.comp he_mp)
  have h := hmp.lintegral_comp hF
  rw [← hT] at h
  exact h

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_update_sub_shear' : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : (ι → ℂ) → ℂ), Measurable g → (∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v) → ∀ F : (ι → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  atlas_forward_decl GlobalTheory.lintegral_update_sub_shear
end

section
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin4
noncomputable section

def pw (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-(4 / 3 : ℝ))

theorem lintegral_pw_lt_top : ∫⁻ t : ℂ, ENNReal.ofReal (pw t) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  convert h.lintegral_lt_top using 4
  simp only [pw]; norm_num

theorem gB_eq (w : Low 4 → ℂ) (p0 : ℕ) : gB p0 w =
    (colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 ^ 2 * colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 ^ 2)⁻¹ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := blkW p0 w
  show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹
  rw [Fin.prod_univ_three]
  have h0 : colGram M (Fin.castSucc 0) = 1 := by simp [colGram, lminor]
  rw [h0]
  simp only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]
  rfl

theorem pw_nonneg (t : ℂ) : 0 ≤ pw t := by unfold pw; positivity

theorem measurable_pw : Measurable fun t : ℂ => ENNReal.ofReal (pw t) := by
  unfold pw; fun_prop

theorem blkW_diag (w : Low 4 → ℂ) (p0 : ℕ) : ∀ i, (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i i = 1 := by
  intro i; fin_cases i <;> simp [blkW, lowMat]

theorem blkW_upper (w : Low 4 → ℂ) (p0 : ℕ) :
    ∀ i j : Fin 3, i < j → (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]

theorem gB_eq_entries (p0 : ℕ) (pa pb pc : Low 4) (w : Low 4 → ℂ)
    (ha : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 0 = w pa)
    (hb : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 0 = w pb)
    (hc : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 1 = w pc) :
    gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.columnGramDeterminant_unitLower_three (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)
  rw [gB_eq, h1, h2, ha, hb, hc]

theorem lintegral_hB_lt_top_of_pos (p0 : ℕ) (pa pb pc : Low 4) (hab : pa ≠ pb) (hcb : pc ≠ pb)
    (hac : pa ≠ pc)
    (hg : ∀ w : Low 4 → ℂ, gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹)
    (hmix : ∀ p : Low 4, p ≠ pa → p ≠ pb → p ≠ pc → (p.1.2 : ℕ) < p0 ∧ p0 ≤ (p.1.1 : ℕ)) :
    ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  set S : Finset (Low 4) := {pa, pb, pc} with hS
  let f : Low 4 → ℂ → ℝ≥0∞ := fun p x =>
    if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact measurable_pw
    · simp only [f, hp, if_false]; exact measurable_one.indicator measurableSet_closedBall
  let U : (Low 4 → ℂ) → ℝ≥0∞ := fun w => ∏ p, f p (w p)
  have hU : Measurable U := Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)
  have hUfin : ∫⁻ w, U w < ⊤ := by
    have := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ))
      (fun p => (hf p).aemeasurable)
    rw [volume_pi, this]
    refine ENNReal.prod_lt_top fun p _ => ?_
    by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact lintegral_pw_lt_top
    · simp only [f, hp, if_false]
      rw [lintegral_indicator measurableSet_closedBall]
      simpa using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))
  have hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) →
      U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc)) := by
    intro w hw
    simp only [U, f]
    rw [Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_singleton, mul_assoc]
      · simpa using hcb.symm
      · simp [hab, hac]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Set.indicator, hw p hp]
  have hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc)) := by
    intro w
    by_cases hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    · have hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1 := fun p hp => by
        have h1 : p ≠ pa := fun h => hp (by simp [hS, h])
        have h2 : p ≠ pb := fun h => hp (by simp [hS, h])
        have h3 : p ≠ pc := fun h => hp (by simp [hS, h])
        obtain ⟨k1, k2⟩ := hmix p h1 h2 h3
        exact hw p k1 k2
      have hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1 := fun p hp => by
        have : p ≠ pb := fun h => hp (by simp [hS, h])
        rw [Function.update_of_ne this]; exact hw' p hp
      rw [hUeq w hw', hUeq _ hw'']
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]
      have n1 := pw_nonneg (w pa)
      have n2 := pw_nonneg (w pb)
      have n3 := pw_nonneg (w pc)
      have n4 := pw_nonneg (w pb - w pa * w pc)
      unfold hB
      rw [Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hg w]
      have key := GlobalTheory.T.flagGram_density_inequality_complex (w pa) (w pb) (w pc)
      have e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        simp only [pw, norm_sub_rev (w pb)]
      rw [e]
      simp only [pw]
      calc _ ≤ _ := key
        _ = _ := by ring
    · unfold hB; rw [Set.indicator_of_notMem hw]; exact zero_le'
  have hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc :=
    (measurable_pi_apply pa).mul (measurable_pi_apply pc)
  have hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc := by
    intro w v h; rw [h pa hab, h pc hcb]
  calc ∫⁻ w, hB p0 w ≤ ∫⁻ w, (U w + U (Function.update w pb (w pb - w pa * w pc))) :=
        lintegral_mono hpt
    _ = (∫⁻ w, U w) + ∫⁻ w, U (Function.update w pb (w pb - w pa * w pc)) :=
        lintegral_add_left hU _
    _ = (∫⁻ w, U w) + ∫⁻ w, U w := by
        rw [GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩

theorem lintegral_hB_four_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  rintro p0 (rfl | rfl)
  · exact lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)
  · exact lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)
end
end GlobalTheory.IntBall.Fin4
end

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  atlas_forward_decl GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top
end

section
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
  GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped ENNReal Matrix

theorem prod_inv_sq_mul_rpow_le {q : ℕ} {t s : ℝ} (d g : Fin q → ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hs : 2 * (q : ℝ) ≤ s) (hg : ∀ k, 0 < g k) (hdg : ∀ k, t * g k ≤ d k) :
    (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ∏ k, g k ^ (-2 : ℤ) := by
  have h1 : ∏ k, (d k ^ 2)⁻¹ ≤ ∏ k, (t ^ 2)⁻¹ * (g k ^ 2)⁻¹ := by
    refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by have := hg k; positivity) (pow_le_pow_left₀ (by have := hg k; positivity) (hdg k) 2)
  have h2 : t ^ s ≤ t ^ (2 * (q : ℝ)) := Real.rpow_le_rpow_of_exponent_ge ht ht1 hs
  have h3 : t ^ (2 * (q : ℝ)) = (t ^ 2) ^ q := by
    rw [Real.rpow_mul ht.le, Real.rpow_two, Real.rpow_natCast]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  calc (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ((t ^ 2)⁻¹ ^ q * ∏ k, (g k ^ 2)⁻¹) * (t ^ 2) ^ q := by
        refine mul_le_mul h1 (h2.trans h3.le) (by positivity) (by positivity)
    _ = ∏ k, g k ^ (-2 : ℤ) := by
        rw [mul_comm, ← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]
        exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_ofNat]

theorem prod_fin_split {r : ℕ} (hr : 1 ≤ r) (f : Fin r → ℝ) :
    ∏ i, f i = f ⟨0, by omega⟩ * ∏ k : Fin (r - 1), f ⟨k + 1, by omega⟩ := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  rw [Fin.prod_univ_succ]
  rfl

theorem colGram_zero {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) : colGram M 0 = 1 := by
  simp [colGram, lminor, Matrix.det_isEmpty]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_dmin_zero (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (h : 0 < r + 1) :
    ‖dmin X.Gm x τ ⟨0, h⟩‖ = 1 := by
  simp [dmin, lminor, Matrix.det_isEmpty]

theorem ball_cases {X : Data E r} (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3) :
    X.p0 = 1 ∨ X.p0 + 1 = r := by
  by_contra hc
  push_neg at hc
  have ha : 2 ≤ X.p0 := by omega
  have hb : 2 ≤ r - X.p0 := by omega
  have := Nat.mul_le_mul ha hb
  omega

theorem exp_neg_rho {X : Data E r} {z : V (nd X)} (hz : z ∈ Om X) (s : ℝ) :
    Real.exp (-(s * rho X z)) = ∏ τ, zDet X z τ ^ s := by
  have e : -(s * rho X z) = ∑ τ, Real.log (zDet X z τ) * s := by
    simp only [rho, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e, Real.exp_sum]
  exact Finset.prod_congr rfl fun τ _ => (Real.rpow_def_of_pos (zDet_pos X hz τ) s).symm

theorem density_mul_exp_le (X : Data E r) (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3)
    (x0 : Base X) {z : V (nd X)} (hz : z ∈ Om X) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    density X x0 z * Real.exp (-(s * rho X z)) ≤ bnd X z := by
  have hcase := ball_cases h1 h2 h3
  have hq : 2 * ((r - 1 : ℕ) : ℝ) ≤ s := by
    rw [Nat.cast_sub (by omega)]
    simpa using hs
  have hle : ∀ τ, zDet X z τ ≤ 1 := GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball E r X hcase z hz
  unfold density bnd
  rw [exp_neg_rho hz, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (zDet_pos X hz τ).le s)) fun τ _ => ?_
  rw [prod_fin_split (by omega)]
  simp only [Fin.castSucc_mk]
  rw [show (‖dmin X.Gm (point X x0 z) τ ⟨0, by omega⟩‖ ^ 2)⁻¹ = 1 by
    rw [norm_dmin_zero]; norm_num, one_mul]
  rcases hcase with hp | hp
  · exact prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.castSucc) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_first E r X hp x0 z hz τ k)
  · have := prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.succ) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last E r X hp x0 z hz τ k)
    refine this.trans_eq ?_
    have e1 := Fin.prod_univ_succ fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    have e2 := Fin.prod_univ_castSucc fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    rw [colGram_zero, one_zpow, one_mul] at e1
    rw [GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one r X.p0 (zOf X z τ), one_zpow, mul_one] at e2
    rw [← e1, e2]
    rfl

theorem block_fin {p0 : ℕ} (h1 : 0 < p0) (h2 : p0 < r) (h3 : p0 * (r - p0) ≤ 3) :
    ∫⁻ w : Low r → ℂ, hB p0 w < ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = p0 + k + 1 := ⟨r - p0 - 1, by omega⟩
  have h3' : p0 * (k + 1) ≤ 3 := by simpa [show p0 + k + 1 - p0 = k + 1 by omega] using h3
  have hr : p0 + k ≤ 3 := by nlinarith
  have hp : p0 ≤ 3 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p0 <;> interval_cases k <;> first
    | omega
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top _ (by decide)
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top _ (by decide)

theorem lintegral_lt_top (X : Data E r) (x0 : Base X) (h1 : 0 < X.p0) (h2 : X.p0 < r)
    (h3 : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 < ⊤ := by
  have hm : Measurable fun z : V (nd X) => ∏ τ, hB X.p0 (zOf X z τ) := by
    refine Finset.measurable_prod _ fun τ _ => (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0).comp ?_
    exact measurable_pi_lambda _ fun p => (EuclideanSpace.proj (𝕜 := ℂ) _).continuous.measurable
  rw [GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain E r X x0 s]
  calc ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z)))
      ≤ ∫⁻ z in Om X, ∏ τ, hB X.p0 (zOf X z τ) := by
        refine setLIntegral_mono hm fun z hz => ?_
        rw [← ENNReal.ofReal_mul (by unfold density; positivity)]
        exact (ENNReal.ofReal_le_ofReal (density_mul_exp_le X h1 h2 h3 x0 hz hs)).trans
          (GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff E r X z hz)
    _ ≤ ∫⁻ z, ∏ τ, hB X.p0 (zOf X z τ) := setLIntegral_le_lintegral _ _
    _ = ∏ _τ : X.Ψ, ∫⁻ w, hB X.p0 w := GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod E r X _ (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0)
    _ < ⊤ := ENNReal.prod_lt_top fun _ _ => block_fin h1 h2 h3

theorem intBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 →
    X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧
      ∀ x1 : Frame X.Ψ r, IsOrth X x1 →
        ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  intro E _ _ _ r X h1 h2 h3 s hs
  have h0 : IsOrth X (x0F X) := GlobalTheory.OrthNear.isOrth_x0F X
  refine ⟨_, lintegral_lt_top X ⟨x0F X, h0⟩ h1 h2 h3 hs, fun x1 hx1 => ?_⟩
  rw [GlobalTheory.Up.PoleValue.rhF_eq h0 hx1, GlobalTheory.Up.PoleValue.muF_eq h0 hx1]

end GlobalTheory.IntBall
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_bound_lintegral_flagDomain_ball_case : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  atlas_forward_decl GlobalTheory.IntBall.intBall
end
