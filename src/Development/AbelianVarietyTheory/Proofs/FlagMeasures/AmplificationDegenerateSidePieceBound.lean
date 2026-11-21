import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetNotGG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_dual_vector_pairing_bounded_majorant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → ∀ b : Fin r, b.val < j → ∀ u : (Fin (2 * r + k + 1) → ℂ), eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ u) ≤ R₀ → ‖herm (Hpk k r) ((sEl k r j β q)⁻¹ *ᵥ bvec (esI k r b)) u‖ ≤ R₀ ^ (2 * r) * De := by
  first | exact @GlobalTheory.Amp.NfComp.herm_sEl_inv_le | exact GlobalTheory.Amp.NfComp.herm_sEl_inv_le | (intros; apply GlobalTheory.Amp.NfComp.herm_sEl_inv_le <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SecBound

variable {k r : ℕ}

def midVec (k r : ℕ) (w : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then w ⟨i.val - r, by omega⟩ else 0

theorem wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

theorem midVec_wI (w : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : midVec k r w (wI k r j) = w j := by
  have hj := j.isLt
  unfold midVec
  rw [dif_pos (by simp only [wI]; omega)]
  congr 1
  apply Fin.ext; simp [wI]

theorem mem_range_wI {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) : i ∈ Set.range (wI k r) :=
  ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩

theorem midVec_out (w : Fin (k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (h : i ∉ Set.range (wI k r)) :
    midVec k r w i = 0 := by
  unfold midVec
  rw [dif_neg fun h' => h (mem_range_wI h')]

theorem midVec_inWb (w : Fin (k + 1) → ℂ) : inWb k r (midVec k r w) := by
  intro i hi
  unfold midVec
  rw [dif_neg (by omega)]

theorem sum_wI (w : Fin (k + 1) → ℂ) : ∑ j, w j • bvec (wI k r j) = midVec k r w := by
  ext i
  by_cases h : i ∈ Set.range (wI k r)
  · obtain ⟨j, rfl⟩ := h
    rw [midVec_wI]
    simp [bvec, Pi.single_apply, wI_inj.eq_iff]
  · rw [midVec_out w h]
    simp only [Finset.sum_apply, Pi.smul_apply, bvec]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne (fun e => h ⟨j, e.symm⟩), smul_zero]

theorem eucl_midVec (w : Fin (k + 1) → ℂ) : eucl (midVec k r w) = eucl w := by
  unfold eucl
  congr 1
  symm
  refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
  · simp [midVec_out w hi]
  · rw [midVec_wI]

theorem mEmb_midVec (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (w : Fin (k + 1) → ℂ) :
    mEmb k r m *ᵥ midVec k r w = midVec k r (m *ᵥ w) := by
  ext i
  have h1 : (mEmb k r m *ᵥ midVec k r w) i = ∑ j, mEmb k r m i (wI k r j) * w j := by
    symm
    refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
    · simp [midVec_out w hi]
    · simp only [midVec_wI]
  rw [h1]
  by_cases h : i ∈ Set.range (wI k r)
  · obtain ⟨l, rfl⟩ := h
    rw [midVec_wI]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    have hl := l.isLt
    unfold mEmb
    rw [dif_pos (by simp only [wI]; omega)]
    congr 2 <;> (apply Fin.ext; simp [wI])
  · rw [midVec_out _ h]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold mEmb
    rw [dif_neg (fun h' => h (mem_range_wI h'.1)), if_neg (fun e => h ⟨j, e.symm⟩), zero_mul]

theorem mEmb_bvec (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : mEmb k r m *ᵥ bvec i = bvec i := by
  ext l
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold mEmb
  rw [dif_neg (by omega)]

theorem eucl_smul_bvec {n : ℕ} (c : ℂ) (i : Fin n) : eucl (c • bvec i) = ‖c‖ := by
  unfold eucl
  rw [Finset.sum_eq_single i]
  · simp [bvec, Complex.normSq_eq_norm_sq]
  · intro b _ hb; simp [bvec, Pi.single_eq_of_ne hb]
  · simp

theorem herm_bvec {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    herm G v (bvec i) = ∑ l, G i l * v l := by
  have : star (bvec i) = Pi.single i (1 : ℂ) := by
    ext l; simp [bvec, Pi.single_apply]
  unfold herm
  rw [this, single_one_dotProduct]; rfl

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, Finset.sum_eq_single (esI k r a)]
  · unfold Hpk
    rw [if_pos (by simp only [eI, esI]; omega), one_mul]
  · intro b _ hb
    have hb' : b.val ≠ 2 * r + k - a.val := fun e => hb (Fin.ext e)
    unfold Hpk
    rw [if_neg (by simp only [eI]; omega), if_neg (by simp only [eI]; omega),
      if_neg (by simp only [eI]; omega), zero_mul]
  · simp

theorem herm_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, Finset.sum_eq_single (eI k r a)]
  · unfold Hpk
    rw [if_neg (by simp only [eI, esI]; omega), if_pos (by simp only [eI, esI]; omega), one_mul]
  · intro b _ hb
    have hb' : b.val ≠ a.val := fun e => hb (Fin.ext e)
    unfold Hpk
    rw [if_neg (by simp only [esI]; omega), if_neg (by simp only [esI]; omega),
      if_neg (by simp only [esI]; omega), zero_mul]
  · simp

theorem Hpk_mulVec_wI (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = (Hb k *ᵥ fun l => v (wI k r l)) j := by
  have hj := j.isLt
  unfold Hb
  rw [Matrix.mulVec_diagonal]
  show ∑ l, Hpk k r (wI k r j) l * v l = _
  rw [Finset.sum_eq_single (wI k r j)]
  · unfold Hpk
    rw [if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega),
      if_pos ⟨by simp only [wI]; omega, by simp only [wI]; omega, rfl⟩]
    congr 1
    simp [wI, Fin.ext_iff]
  · intro b _ hb
    unfold Hpk
    rw [if_neg (by simp only [wI]; omega), if_neg (by simp only [wI]; omega),
      if_neg (fun h => hb h.2.2.symm), zero_mul]
  · simp

theorem herm_midVec (v : Fin (2 * r + k + 1) → ℂ) (w : Fin (k + 1) → ℂ) :
    herm (Hpk k r) v (midVec k r w) = herm (Hb k) (fun l => v (wI k r l)) w := by
  unfold herm dotProduct
  symm
  refine Fintype.sum_of_injective (wI k r) wI_inj _ _ (fun i hi => ?_) (fun j => ?_)
  · simp [midVec_out w hi]
  · simp only [Pi.star_apply, midVec_wI, Hpk_mulVec_wI]

theorem herm_UH {n : ℕ} {G m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UH G) (v w : Fin n → ℂ) :
    herm G (m *ᵥ v) (m *ᵥ w) = herm G v w := by
  have h : mᴴ * G * m = G := hm
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem UH_mul {n : ℕ} {G g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) (hh : h ∈ UH G) : g * h ∈ UH G := by
  have h1 : gᴴ * G * g = G := hg
  have h2 : hᴴ * G * h = G := hh
  show (g * h)ᴴ * G * (g * h) = G
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * G * (g * h) = hᴴ * (gᴴ * G * g) * h := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2]

theorem isUnit_det_of_UH {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) : IsUnit m.det := by
  have h : mᴴ * Hb k * m = Hb k := hm
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul] at h2
  have h3 : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs <;> simp
  refine isUnit_iff_ne_zero.2 fun e => h3 ?_
  rw [← h2, e, mul_zero]

theorem eucl_eq_norm {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_Hb (v : Fin (k + 1) → ℂ) : eucl (Hb k *ᵥ v) = eucl v := by
  unfold eucl Hb
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem norm_herm_Hb_le (v w : Fin (k + 1) → ℂ) : ‖herm (Hb k) v w‖ ≤ eucl v * eucl w := by
  rw [← eucl_Hb v, eucl_eq_norm, eucl_eq_norm, mul_comm]
  refine le_trans (le_of_eq ?_) (norm_inner_le_norm (𝕜 := ℂ) _ _)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]; rfl

theorem herm_Hb_self (v : Fin (k + 1) → ℂ) : herm (Hb k) v (Hb k *ᵥ v) = ((eucl v ^ 2 : ℝ) : ℂ) := by
  rw [← eucl_Hb v, eucl, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)]
  unfold herm dotProduct
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem eucl_le_of_herm (v : Fin (k + 1) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ w, eucl w ≤ 1 → ‖herm (Hb k) v w‖ ≤ M) : eucl v ≤ M := by
  have h0 : 0 ≤ eucl v := Real.sqrt_nonneg _
  rcases h0.eq_or_lt with e | hpos
  · rw [← e]; exact hM
  have h1 := h ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) (by
    rw [eucl_eq_norm, WithLp.toLp_smul, norm_smul, ← eucl_eq_norm, eucl_Hb, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 h0), inv_mul_cancel₀ hpos.ne'])
  have h2 : herm (Hb k) v ((((eucl v)⁻¹ : ℝ) : ℂ) • (Hb k *ᵥ v)) = ((eucl v : ℝ) : ℂ) := by
    have := herm_Hb_self v
    unfold herm at this ⊢
    rw [star_smul, smul_dotProduct, this, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rwa [h2, Complex.norm_real, Real.norm_of_nonneg h0] at h1

theorem eI_inj : Function.Injective (eI k r) := fun _ _ h => Fin.ext (by simpa [eI] using congrArg Fin.val h)

theorem esI_inj : Function.Injective (esI k r) := by
  intro a b h
  have := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  simp only [esI] at this
  exact Fin.ext (by omega)

def xVec (k r : ℕ) (x : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ a, x a • bvec (eI k r a)

def yVec (k r : ℕ) (x : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ a, x a • bvec (esI k r a)

theorem xVec_eI (x : Fin r → ℂ) (a : Fin r) : xVec k r x (eI k r a) = x a := by
  simp [xVec, bvec, Pi.single_apply, eI_inj.eq_iff]

theorem yVec_esI (x : Fin r → ℂ) (a : Fin r) : yVec k r x (esI k r a) = x a := by
  simp [yVec, bvec, Pi.single_apply, esI_inj.eq_iff]

theorem xVec_out (x : Fin r → ℂ) {i : Fin (2 * r + k + 1)} (hi : r ≤ i.val) : xVec k r x i = 0 := by
  simp only [xVec, Finset.sum_apply, Pi.smul_apply, bvec]
  refine Finset.sum_eq_zero fun a _ => ?_
  have ha := a.isLt
  rw [Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [eI] at this; omega), smul_zero]

theorem yVec_out (x : Fin r → ℂ) {i : Fin (2 * r + k + 1)} (hi : i.val ≤ r + k) : yVec k r x i = 0 := by
  simp only [yVec, Finset.sum_apply, Pi.smul_apply, bvec]
  refine Finset.sum_eq_zero fun a _ => ?_
  have ha := a.isLt
  rw [Pi.single_eq_of_ne (fun e => by have := congrArg Fin.val e; simp only [esI] at this; omega), smul_zero]

theorem uEmb_xVec {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det) (x : Fin r → ℂ) :
    uEmb k r u *ᵥ xVec k r x = xVec k r (u *ᵥ x) := by
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1
  unfold xVec
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem inv_mulVec_esI (B : Fin r → Fin (k + 1) → ℂ) {S u : Matrix (Fin r) (Fin r) ℂ} (hS : Sᴴ = -S)
    (hu : IsUnit u.det) (b : Fin r) :
    (pEl k r B S * uEmb k r u)⁻¹ *ᵥ bvec (esI k r b) =
      yVec k r (fun a => star (u b a)) + midVec k r (-B b) +
        xVec k r (u⁻¹ *ᵥ fun a => -S a b - herm (Hb k) (B b) (B a) / 2) := by
  have hu' : IsUnit u⁻¹.det := Matrix.isUnit_nonsing_inv_det u hu
  have h1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1
  have h2 := (GlobalTheory.Amp.Rad.radical k r).1
  rw [Matrix.mul_inv_rev, (h1 u hu).2.1, ((h2 B S).2.2.2 hS).2, ← Matrix.mulVec_mulVec, (h2 (-B) (-S)).2.2.1,
    Matrix.mulVec_add, Matrix.mulVec_add, (h1 _ hu').2.2.2.1, sum_wI, (h1 _ hu').2.2.2.2 _ (midVec_inWb _),
    Matrix.nonsing_inv_nonsing_inv u hu, ← uEmb_xVec hu']
  congr 2
  unfold xVec
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  simp [herm, Matrix.mulVec_neg]

theorem isUnit_det_diag {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) :
    IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'

theorem inv_diag {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) :
    (Matrix.diagonal fun b => (a b : ℂ))⁻¹ = Matrix.diagonal fun b => (a b : ℂ)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ha b).ne')

theorem eucl_levi {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) :
    (∀ b, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (eI k r b)) = (a b)⁻¹) ∧
    (∀ b, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ bvec (esI k r b)) = a b) ∧
    ∀ w, eucl ((uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)⁻¹ *ᵥ midVec k r (m *ᵥ w)) = eucl w := by
  have hu := isUnit_det_diag ha
  have hu' := Matrix.isUnit_nonsing_inv_det _ hu
  have h1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1
  have h2 := ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).2
  rw [Matrix.mul_inv_rev, (h1 _ hu).2.1, h2]
  refine ⟨fun b => ?_, fun b => ?_, fun w => ?_⟩
  · have hb := b.isLt
    rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.1, inv_diag ha, Finset.sum_eq_single b, Matrix.mulVec_smul,
      mEmb_bvec _ (Or.inl (by simp only [eI]; omega)), eucl_smul_bvec]
    · simp [abs_of_pos (ha b)]
    · intro c _ hc; simp [Matrix.diagonal_apply_ne _ hc]
    · simp
  · have hb := b.isLt
    rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.1, Matrix.nonsing_inv_nonsing_inv _ hu, Finset.sum_eq_single b,
      Matrix.mulVec_smul, mEmb_bvec _ (Or.inr (by simp only [esI]; omega)), eucl_smul_bvec]
    · simp [abs_of_pos (ha b)]
    · intro c _ hc; simp [Matrix.diagonal_apply_ne _ hc.symm]
    · simp
  · rw [← Matrix.mulVec_mulVec, (h1 _ hu').2.2.2.2 _ (midVec_inWb _), mEmb_midVec, eucl_midVec,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_UH hm), Matrix.one_mulVec]

theorem mem_Sset_of_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem torus_le {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n n' : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    {a : Fin r → ℝ} (ha : ∀ b, 0 < a b) {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) {R : ℝ}
    (h : Sg2 k r z (n * n' * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R) (b : Fin r) :
    (a b)⁻¹ ≤ R ∧ a b ≤ R := by
  have hl := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  have hx : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r :=
    UH_mul ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 _ (isUnit_det_diag ha)).1 ((GlobalTheory.Amp.Rad.radical k r).2.2.2.2 m hm).1
  have h1 : (1 : Mat k r) ∈ GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r)) :=
    ⟨by show (1 : Mat k r)ᴴ * _ * 1 = _; simp, one_mem _⟩
  have e1 := (hl.1 _ hx n' (mem_Sset_of_Nset z hn') 1 h1).1 b.castSucc
  have e2 := (hl.1 _ (UH_mul hn'.1 hx) n (mem_Sset_of_Nset z hn) 1 h1).1 b.castSucc
  rw [Matrix.mul_one] at e1 e2
  have e3 := hl.2.1 a ha m hm b
  have h2 := ((Finset.fold_max_le _).1 h).2 b.castSucc (Finset.mem_univ _)
  rw [Matrix.mul_assoc, e2, e1, e3, inv_inv, max_le_iff] at h2
  exact h2

theorem section_coord_le (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hN : IsNormal0 k r hj β c z z' g₀) (De R₀ : ℝ)
    (hD : DeOK k r z z' g₀ De) (hR : 1 ≤ R₀) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k))
    (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (h1 : Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀)
    (h2 : Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀) :
    (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧
      (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  have key := GlobalTheory.T.moved_dual_vector_pairing_bounded_majorant k r j hj z z' g₀ β c hz hz' hT hN De R₀ hD hR m hm q a ha h1 h2
  have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hD.1
  generalize R₀ ^ (2 * r) * De = M at key hM ⊢
  obtain ⟨B, hB⟩ : ∃ B : Fin r → Fin (k + 1) → ℂ, B = fun a => if h : a.val < j then q.1.1 ⟨a, h⟩ else 0 := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin r) (Fin r) ℂ, S = skewM
    (fun p => if h : p.1.1.val < j then q.1.2.1 ⟨p, h⟩ else 0) (fun a => if h : a.val < j then q.1.2.2 ⟨a, h⟩ else 0) :=
    ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Matrix (Fin r) (Fin r) ℂ, u = upperOff β q.2 := ⟨_, rfl⟩
  have hs : sEl k r j β q = pEl k r B S * uEmb k r u := by rw [hB, hSdef, hudef]; rfl
  have hS : Sᴴ = -S := hSdef ▸ (GlobalTheory.Amp.Rad.radical k r).2.1 _ _
  have hu1 := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 (fun p => if h : β p.1.1 ≠ β p.1.2 then q.2 ⟨p, h⟩ else 0)
  have hu : IsUnit u.det := by
    rw [hudef, upperOff, hu1.1]; exact isUnit_one
  have huN : uEmb k r u ∈ Nset k r := hudef ▸ hu1.2
  rw [hs] at key h1
  have hpN := (((GlobalTheory.Amp.Rad.radical k r).1 B S).2.2.2 hS).1
  have ht := torus_le hz' hpN huN ha hm h1
  have hl := eucl_levi (k := k) ha hm
  simp only [inv_mulVec_esI B hS hu] at key
  have hmm : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_UH hm)

  have k1 : ∀ b : Fin r, b.val < j → ∀ d, ‖u b d‖ ≤ M := by
    intro b hb d
    have hd := d.isLt
    have := key b hb _ ((hl.1 d).le.trans (ht d).1)
    rwa [herm_eI, Pi.add_apply, Pi.add_apply, yVec_esI, midVec_inWb _ _ (Or.inr (by simp only [esI]; omega)),
      xVec_out _ (by simp only [esI]; omega), add_zero, add_zero, norm_star] at this
  have c1 : ∀ p, ‖q.2 p‖ ≤ M := by
    intro p
    have hlt : p.1.1.1 < p.1.1.2 := p.1.2
    have hb : p.1.1.1.val < j := by
      by_contra hc
      have hlt' : p.1.1.1.val < p.1.1.2.val := hlt
      exact p.2 ((hN.2.2.2.2.1 _ _ (by omega)).2 (by omega))
    have := k1 _ hb p.1.1.2
    rw [hudef, upperOff, upper, dif_pos hlt, dif_pos p.2] at this
    exact this
  have k1' : ∀ b d, ‖u b d‖ ≤ M := by
    intro b d
    rw [hudef, upperOff, upper]
    split_ifs
    · exact c1 _
    · simpa using le_trans zero_le_one hM
    · simpa using hM
    · simpa using le_trans zero_le_one hM

  have k2 : ∀ b : Fin r, eucl (m⁻¹ *ᵥ B b) ≤ M := by
    intro b
    by_cases hb : b.val < j
    · refine eucl_le_of_herm _ (le_trans zero_le_one hM) fun w hw => ?_
      have := key b hb _ (((hl.2.2 w).le.trans hw).trans hR)
      rw [herm_midVec] at this
      have e : (fun l => (yVec k r (fun a => star (u b a)) + midVec k r (-B b) +
          xVec k r (u⁻¹ *ᵥ fun a => -S a b - herm (Hb k) (B b) (B a) / 2)) (wI k r l)) = -B b := by
        funext l
        have hl' := l.isLt
        rw [Pi.add_apply, Pi.add_apply, midVec_wI, yVec_out _ (by simp only [wI]; omega),
          xVec_out _ (by simp only [wI]; omega), zero_add, add_zero]
      rw [e] at this
      rw [← herm_UH hm, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
      simpa [herm, Matrix.mulVec_neg] using this
    · have : B b = 0 := by rw [hB]; exact dif_neg hb
      rw [this]
      simpa [eucl] using le_trans zero_le_one hM
  have k2' : ∀ b d, ‖herm (Hb k) (B b) (B d)‖ ≤ M ^ 2 := by
    intro b d
    have e : herm (Hb k) (B b) (B d) = herm (Hb k) (m⁻¹ *ᵥ B b) (m⁻¹ *ᵥ B d) := by
      rw [← herm_UH hm (m⁻¹ *ᵥ B b), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec, Matrix.one_mulVec]
    rw [e, sq]
    exact (norm_herm_Hb_le _ _).trans (mul_le_mul (k2 b) (k2 d) (Real.sqrt_nonneg _) (le_trans zero_le_one hM))

  have k3 : ∀ b : Fin r, b.val < j → ∀ d, ‖S d b‖ ≤ 2 * r * M ^ 2 := by
    intro b hb d
    obtain ⟨x, hx⟩ : ∃ x : Fin r → ℂ, x = fun a => -S a b - herm (Hb k) (B b) (B a) / 2 := ⟨_, rfl⟩
    have hy : ∀ e, ‖(u⁻¹ *ᵥ x) e‖ ≤ M := by
      intro e
      have he := e.isLt
      have := key b hb _ ((hl.2.1 e).le.trans (ht e).2)
      rwa [herm_esI, Pi.add_apply, Pi.add_apply, xVec_eI, midVec_inWb _ _ (Or.inl (by simp only [eI]; omega)),
        yVec_out _ (by simp only [eI]; omega), zero_add, zero_add, ← hx] at this
    have hxd : ‖x d‖ ≤ r * M ^ 2 := by
      have e : x d = ∑ e, u d e * (u⁻¹ *ᵥ x) e := by
        conv_lhs => rw [← Matrix.one_mulVec x, ← Matrix.mul_nonsing_inv u hu, ← Matrix.mulVec_mulVec]
        rfl
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ e, ‖u d e * (u⁻¹ *ᵥ x) e‖ ≤ ∑ _e : Fin r, M ^ 2 := Finset.sum_le_sum fun e _ => by
            rw [norm_mul, sq]
            exact mul_le_mul (k1' d e) (hy e) (norm_nonneg _) (le_trans zero_le_one hM)
        _ = r * M ^ 2 := by simp
    have e : S d b = -(x d + herm (Hb k) (B b) (B d) / 2) := by rw [hx]; ring
    have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have h3 := k2' b d
    have h4 : 0 ≤ M ^ 2 := sq_nonneg _
    rw [e, norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_two]
    nlinarith
  refine ⟨c1, fun b => ?_, fun p => ?_, fun b => ?_⟩
  · have := k2 b.1
    have e : B b.1 = q.1.1 b := by rw [hB]; exact dif_pos b.2
    rwa [e] at this
  · have hlt : p.1.1.1 < p.1.1.2 := p.1.2
    have := k3 _ p.2 p.1.1.2
    rw [hSdef, skewM, dif_neg (not_lt.2 hlt.le), dif_pos hlt, dif_pos p.2, norm_neg, norm_star] at this
    exact this
  · have := k3 _ b.2 b.1
    rw [hSdef, skewM, dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), dif_pos b.2] at this
    simpa using this

end GlobalTheory.Amp.SecBound
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_height_bound_section : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧ (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  atlas_forward_decl GlobalTheory.Amp.SecBound.section_coord_le
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormalGram

variable {k r : ℕ}

def mid (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  have hi := i.2
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, rfl⟩
  by_cases h2 : i.val ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)

theorem wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

theorem sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : inWb k r f) : ∑ i, f i = ∑ j, f (wI k r j) := by
  symm
  refine Finset.sum_of_injOn (wI k r) wI_inj.injOn (by simp) ?_ (by simp)
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, by simp, Fin.ext ?_⟩
  simp only [wI]; omega

theorem mulVec_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i i' : Fin n) (c : ℂ)
    (h : ∀ j, A i j = if j = i' then c else 0) : (A *ᵥ v) i = c * v i' := by
  simp [Matrix.mulVec, dotProduct, h]

theorem H_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  rw [mulVec_of_row _ _ _ (eI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_wI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r b) = (if b = Fin.last k then -1 else 1) * v (wI k r b) := by
  rw [mulVec_of_row _ _ _ (wI k r b) _]
  intro j
  have := b.2; have := j.2
  have e : (wI k r b).val = r + b.val := rfl
  simp only [Hpk, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  rw [← H_eI v a]
  simp [herm, bvec, dotProduct, Pi.single_apply]

theorem herm_mid (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (mid k r v) (mid k r z) := by
  unfold herm dotProduct
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [H_wI]
    simp [Hb, mid, Matrix.mulVec_diagonal]
  · intro i hi
    simp [hz i hi]

theorem mid_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (uEmb k r u *ᵥ v) = mid k r v := by
  funext b
  simp only [mid]
  rw [mulVec_of_row _ _ _ (wI k r b) 1, one_mul]
  intro j
  have := b.2; have := j.2
  simp only [uEmb, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem mid_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (mEmb k r m *ᵥ v) = m *ᵥ mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have := j.2
    congr 1
    have e : (wI k r b).val = r + b.val := rfl
    have e' : (wI k r j).val = r + j.val := rfl
    unfold mEmb
    rw [dif_pos (by omega)]
    congr 1 <;> exact Fin.ext (by simp only []; omega)
  · intro i hi
    simp only [mEmb, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp

theorem top_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mEmb k r m *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [mEmb, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (pEl k r B S *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  have e : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [pEl, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ a, v (esI k r a) = 0) (a : Fin r) :
    (uEmb k r u *ᵥ v) (esI k r a) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := a.2
  rcases idx_cases i with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have := b.2
    simp only [uEmb, esI, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · have := b.2
    simp only [uEmb, esI, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp [hv]

theorem top_uEmb_iff (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (v : Fin (2 * r + k + 1) → ℂ) :
    (∀ a, (uEmb k r u *ᵥ v) (esI k r a) = 0) ↔ ∀ a, v (esI k r a) = 0 := by
  refine ⟨fun h a => ?_, top_uEmb u v⟩
  have h1 := top_uEmb u⁻¹ _ h a
  obtain ⟨hm, h0, -⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  rwa [Matrix.mulVec_mulVec, ← hm _ _ (Matrix.isUnit_nonsing_inv_det u hu) hu, Matrix.nonsing_inv_mul u hu, h0,
    Matrix.one_mulVec] at h1

theorem mid_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a, v (esI k r a) = 0) : mid k r (pEl k r B S *ᵥ v) = mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [Finset.sum_eq_single (wI k r b)]
  · simp [pEl]
  · intro i _ hi
    rcases idx_cases i with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (eI k r c).val = c.val := rfl
      simp only [pEl, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (wI k r c).val = r + c.val := rfl
      simp only [pEl, Fin.ext_iff, ne_eq] at hi ⊢
      split_ifs <;> first | omega | simp
    · simp [hv]
  · simp

theorem mid_pEl_esI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    mid k r (pEl k r B S *ᵥ bvec (esI k r a)) = B a := by
  funext b
  have := a.2; have := b.2
  simp only [mid, bvec, Matrix.mulVec_single_one, Matrix.col_apply, pEl, wI, esI, Fin.ext_iff]
  rw [if_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1 <;> exact Fin.ext (by simp only []; omega)

theorem gramProj_mul {n j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (C : Matrix (Fin j) (Fin j) ℂ)
    (w : Fin j → Fin n → ℂ) : gramProj P (fun a => ∑ b, C b a • w b) = ‖C.det‖ * gramProj P w := by
  unfold gramProj
  have h : (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (∑ b, C b a • w b))) =
      Cᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * C := by
    ext a a'
    simp only [Matrix.gram_apply, WithLp.toLp_sum, WithLp.toLp_smul, map_sum, map_smul, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Complex.star_def]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    show ∀ x y : ℝ, x * y * x = x ^ 2 * y from fun x y => by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem inner_mid (v u : EuclideanSpace ℂ (Fin (2 * r + k + 1))) (hu : inWb k r u.ofLp) :
    ⟪v, u⟫_ℂ = ⟪(WithLp.toLp 2 (mid k r v.ofLp) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 (mid k r u.ofLp)⟫_ℂ := by
  simp only [PiLp.inner_apply]
  rw [sum_mid]
  · rfl
  · intro i hi
    simp [hu i hi]

theorem exists_mid (p : Fin (k + 1) → ℂ) : ∃ u, inWb k r u ∧ mid k r u = p := by
  refine ⟨fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then p ⟨i.val - r, by omega⟩ else 0, ?_, ?_⟩
  · intro i hi
    exact dif_neg (by omega)
  · funext b
    have := b.2
    have e : (wI k r b).val = r + b.val := rfl
    unfold mid
    simp only []
    rw [dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp only []; omega)

theorem gramProj_mid {j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ v, v ∈ P ↔ inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P₀) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    gramProj P v = gramProj P₀ fun a => mid k r (v a) := by
  have key : ∀ y : EuclideanSpace ℂ (Fin (2 * r + k + 1)),
      P₀.starProjection (WithLp.toLp 2 (mid k r y.ofLp)) = WithLp.toLp 2 (mid k r (P.starProjection y).ofLp) := by
    intro y
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hP _).1 (P.starProjection_apply_mem y)).2 ?_
    intro w hw
    obtain ⟨u, hu, hu'⟩ := exists_mid (r := r) w.ofLp
    have hmem : WithLp.toLp 2 u ∈ P := (hP _).2 ⟨hu, by simpa [hu'] using hw⟩
    have h1 := P.starProjection_inner_eq_zero y _ hmem
    rw [inner_mid _ _ hu] at h1
    simp only [hu'] at h1
    exact h1
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply]
  rw [inner_mid _ _ ((hP _).1 (P.starProjection_apply_mem _)).1, ← key, ← key]

def P0 (k : ℕ) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  (Submodule.span ℂ {WithLp.toLp 2 (Pi.single (Fin.last k) 1), WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))})ᗮ

theorem mem_lastZeroOrthImageSubspace_iff (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) (p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ P0 k m ζ ↔ p (Fin.last k) = 0 ∧ herm (Hb k) (m *ᵥ p) ζ = 0 := by
  have e1 : ⟪(WithLp.toLp 2 (Pi.single (Fin.last k) 1) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      p (Fin.last k) := by
    simp [PiLp.inner_apply]
  have e2 : ⟪(WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ)) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      herm (Hb k) (m *ᵥ p) ζ := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm, Matrix.star_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
  unfold P0
  rw [Submodule.span_insert, ← Submodule.inf_orthogonal, Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_orthogonal_singleton_iff_inner_right, e1, e2]

theorem finrank_lastZeroOrthImageSubspace_ge (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    k - 1 ≤ Module.finrank ℂ (P0 k m ζ) := by
  classical
  unfold P0
  set a : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (Pi.single (Fin.last k) 1)
  set b : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))
  have h1 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℂ ({a, b} : Set _))
  have h2 : Module.finrank ℂ (Submodule.span ℂ ({a, b} : Set _)) ≤ 2 := by
    have := finrank_span_finset_le_card (R := ℂ) ({a, b} : Finset _)
    have e : ((({a, b} : Finset _)) : Set (EuclideanSpace ℂ (Fin (k + 1)))) = {a, b} := by simp
    rw [← e]
    exact this.trans Finset.card_le_two
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
  omega

theorem mem_Ppos_iff (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (g : Mat k r)
    (hH : ∀ w, w ∈ Hcom k r z z' g ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0)
    (B : Fin r → Fin (k + 1) → ℂ) (S u t : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (ht : IsUnit t.det)
    (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    v ∈ Ppos k r z z' g (pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m)) ↔
      inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P0 k m (mid k r z') := by
  set x := pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m) with hx
  have hxv : x *ᵥ v.ofLp = pEl k r B S *ᵥ (uEmb k r u *ᵥ (uEmb k r t *ᵥ (mEmb k r m *ᵥ v.ofLp))) := by
    simp only [hx, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have htop : (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ↔ ∀ a, v.ofLp (esI k r a) = 0 := by
    simp only [hxv, top_pEl]
    rw [top_uEmb_iff u hu, top_uEmb_iff t ht]
    simp only [top_mEmb]
  have hmid : (∀ a, v.ofLp (esI k r a) = 0) → mid k r (x *ᵥ v.ofLp) = m *ᵥ mid k r v.ofLp := by
    intro h
    rw [hxv, mid_pEl, mid_uEmb, mid_uEmb, mid_mEmb]
    exact top_uEmb _ _ (top_uEmb _ _ (by simpa only [top_mEmb] using h))
  have hf : (∀ a : Fin (r + 1), herm (Hpk k r) (x *ᵥ v.ofLp) (fvec k r z' a) = 0) ↔
      (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ∧ herm (Hpk k r) (x *ᵥ v.ofLp) z' = 0 := by
    constructor
    · intro h
      refine ⟨fun a => ?_, ?_⟩
      · have := h a.castSucc
        rw [← herm_eI (x *ᵥ v.ofLp) a]
        simpa [fvec] using this
      · simpa [fvec] using h (Fin.last r)
    · rintro ⟨h1, h2⟩ a
      unfold fvec
      split_ifs
      · rw [herm_eI]; exact h1 _
      · exact h2
  have hm : v ∈ Ppos k r z z' g x ↔ Hpk k r *ᵥ v.ofLp = v.ofLp ∧ x *ᵥ v.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r := by
    simp only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rfl
  rw [hm, hH, hf, htop, mem_lastZeroOrthImageSubspace_iff, herm_mid _ _ hz']
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hmid h2] at h3
    refine ⟨?_, ?_, h3⟩
    · intro i hi
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
      · rw [← h1, H_eI]; exact h2 a
      · have := b.2
        have e : (wI k r b).val = r + b.val := rfl
        omega
      · exact h2 a
    · have := congrFun h1 (wI k r (Fin.last k))
      rw [H_wI, if_pos rfl] at this
      show v.ofLp (wI k r (Fin.last k)) = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2, h3⟩
    have he : ∀ a, v.ofLp (eI k r a) = 0 := fun a => h1 _ (Or.inl a.2)
    have hs : ∀ a, v.ofLp (esI k r a) = 0 := fun a => h1 _ (Or.inr (by have := a.2; simp only [esI]; omega))
    refine ⟨?_, hs, by rw [hmid hs]; exact h3⟩
    funext i
    rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
    · rw [H_eI, he, hs]
    · rw [H_wI]
      split_ifs with hb
      · have : v.ofLp (wI k r b) = 0 := by rw [hb]; exact h2
        rw [this, mul_zero]
      · rw [one_mul]
    · rw [H_esI, he, hs]

theorem eq_sum_of_mem_XstJ {j : ℕ} (hj : j ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : y ∈ XstJ k r j) :
    y = ∑ b : Fin j, y (esI k r (Fin.castLE hj b)) • bvec (esI k r (Fin.castLE hj b)) := by
  unfold XstJ at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hy
    rw [Finset.sum_eq_single (⟨a.val, ha⟩ : Fin j)]
    · have : Fin.castLE hj ⟨a.val, ha⟩ = a := rfl
      simp [this, bvec]
    · intro b _ hb
      have : esI k r (Fin.castLE hj b) ≠ esI k r a := by
        intro h
        have h1 := congrArg Fin.val h
        have := b.2
        simp only [esI, Fin.val_castLE] at h1
        exact hb (Fin.ext (by simp only []; omega))
      simp [bvec, Pi.single_eq_of_ne this]
    · simp
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← h, ← h']
  | smul c y _ h =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← h]

theorem mid_sum {j : ℕ} (c : Fin j → ℂ) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    mid k r (∑ b, c b • v b) = ∑ b, c b • mid k r (v b) := by
  funext i
  simp [mid, Finset.sum_apply]

theorem Dj_eq {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dj k r hj z z' g = ‖(Matrix.of fun b a : Fin j =>
      (g *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b))).det‖ := by
  unfold Dj Dmin
  congr 2
  ext b a
  have ha : a.val < r := lt_of_lt_of_le a.2 hj
  have hb : b.val < r := lt_of_lt_of_le b.2 hj
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Matrix.of_apply]
  rw [dif_pos ha, dif_pos hb, herm_eI]
  rfl

theorem Yj_eq_gramProj : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  intro k r j hj z z' g β c hz hz' hT hN m hm
  obtain ⟨-, -, -, hD, hD', -, hH⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g β c hz hz' hT hN
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  obtain ⟨hp, hsk, -, -, hM⟩ := GlobalTheory.T.isotropicStabilizerRadical_structure k r
  refine ⟨P0 k m (mid k r z'), finrank_lastZeroOrthImageSubspace_ge _ _, fun q a ha => ?_⟩
  have hu : IsUnit (upperOff β q.2).det := by
    unfold upperOff
    rw [(hup _).1]; exact isUnit_one
  have ht : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  unfold Yj sEl pSec pOf
  rw [gramProj_mid _ _ (mem_Ppos_iff z z' hz' g hH _ _ _ _ hu ht m), div_eq_iff hD.ne', ← hD', Dj_eq, mul_comm (gramProj _ _)]
  set C : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun b a : Fin j =>
      (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b)) with hC
  have hn : ‖C.det‖ = ‖(-C).det‖ := by
    rw [Matrix.det_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hn, ← gramProj_mul]
  congr 1
  funext b
  rw [eq_sum_of_mem_XstJ hj _ (hN.2.2.2.2.2.1 (Fin.castLE hj b) b.2).1, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  rw [mid_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, (hM m hm).2, (hU _ hu).2.1, (hU _ ht).2.1,
    ((hp _ _).2.2.2 (hsk _ _)).2]
  simp only [← Matrix.mulVec_mulVec]
  rw [mid_mEmb, mid_uEmb, mid_uEmb, mid_pEl_esI]
  simp only [Pi.neg_apply, Matrix.neg_apply, hC, Matrix.of_apply, Matrix.mulVec_neg, smul_neg, neg_smul]
  rw [dif_pos (show (Fin.castLE hj d).val < j from d.2)]

end GlobalTheory.Amp.NormalGram
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  atlas_forward_decl GlobalTheory.Amp.NormalGram.Yj_eq_gramProj
end

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem two_mul_pi_pow_le_four_pow (k : ℕ) (hk : 3 ≤ k) : 2 * Real.pi ^ k ≤ (4 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := Real.pi_pos.le
  have h1 : Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := pow_le_pow_left₀ h0 Real.pi_lt_d2.le 3
  have h2 : Real.pi ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ h0 Real.pi_le_four m
  have h3 : 2 * Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by norm_num at h1 ⊢; linarith
  rw [pow_add, pow_add, ← mul_assoc]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

theorem box_volume_arith : ∀ (r j n₁ n₂ n₃ : ℕ) (M : ℝ), 1 ≤ j → j ≤ r → 2 * n₁ ≤ r * (r - 1) → 2 * n₂ ≤ r * (r - 1) → n₃ ≤ r → 1 ≤ M → (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2)) ≤ (4 * r : ℝ) ^ (4 * r ^ 2) * M ^ (8 * r ^ 2) := by
  intro r j n₁ n₂ n₃ M hj hjr h1 h2 h3 hM
  have hr : 1 ≤ r := hj.trans hjr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hM0 : 0 ≤ M := by linarith
  have hA : (1 : ℝ) ≤ 4 * r := by linarith
  have hrr : r * (r - 1) + r = r ^ 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]; ring
  have hjj : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have e : (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2))
      = (Real.pi ^ n₁ * (Real.pi * (2 * r) ^ 2) ^ n₂ * (4 * r) ^ n₃ * (2 * Real.pi ^ (2 * j + j ^ 2))) *
        M ^ (2 * n₁ + 4 * n₂ + 2 * n₃ + 4 * j + 2 * j ^ 2) := by
    have a1 : Real.pi * (2 * r * M ^ 2) ^ 2 = (Real.pi * (2 * r) ^ 2) * M ^ 4 := by ring
    have a2 : 2 * (2 * r * M ^ 2) = (4 * (r : ℝ)) * M ^ 2 := by ring
    rw [a1, a2, mul_pow Real.pi, mul_pow _ (M ^ 4), mul_pow _ (M ^ 2), mul_pow Real.pi (M ^ 2)]
    generalize Real.pi * (2 * (r : ℝ)) ^ 2 = B
    generalize 4 * (r : ℝ) = C
    ring
  rw [e]
  have b1 : Real.pi ^ n₁ ≤ (4 * r : ℝ) ^ n₁ := pow_le_pow_left₀ hpi (by linarith) _
  have b2 : (Real.pi * (2 * r) ^ 2) ^ n₂ ≤ (4 * r : ℝ) ^ (2 * n₂) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (0 : ℝ) ≤ (2 * r) ^ 2 := by positivity
    nlinarith
  have b4 : 2 * Real.pi ^ (2 * j + j ^ 2) ≤ (4 * r : ℝ) ^ (2 * j + j ^ 2) :=
    (two_mul_pi_pow_le_four_pow _ (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hM (by omega)) (by positivity) (by positivity)
  calc _ ≤ (4 * r : ℝ) ^ n₁ * (4 * r : ℝ) ^ (2 * n₂) * (4 * r) ^ n₃ * (4 * r : ℝ) ^ (2 * j + j ^ 2) := by
        gcongr
    _ = (4 * r : ℝ) ^ (n₁ + 2 * n₂ + n₃ + (2 * j + j ^ 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hA (by omega)

end GlobalTheory.Amp
end

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_flagGramNumberNormalized_indicator : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  first | exact @GlobalTheory.Amp.YMeas.yj_measurable | exact GlobalTheory.Amp.YMeas.yj_measurable | (intros; apply GlobalTheory.Amp.YMeas.yj_measurable <;> assumption)
end

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreNormal

theorem vol_discs (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = ENNReal.ofReal ((Real.pi * M ^ 2) ^ Fintype.card ι) := by
  have h : {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Complex.volume_closedBall,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hM, mul_comm]
  congr 2
  exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm

theorem vol_ints (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℝ | ∀ p, |x p| ≤ M} = ENNReal.ofReal ((2 * M) ^ Fintype.card ι) := by
  have h : {x : ι → ℝ | ∀ p, |x p| ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Real.volume_closedBall,
    ENNReal.ofReal_pow (by positivity)]

def lowEquiv {r j : ℕ} (hj : j ≤ r) : Fin j ≃ {a : Fin r // a.val < j} where
  toFun b := ⟨Fin.castLE hj b, b.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vol_reindex {k r j : ℕ} (hj : j ≤ r) (T : Set (Fin j → Fin (k + 1) → ℂ)) :
    volume {B : {a : Fin r // a.val < j} → Fin (k + 1) → ℂ | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈ T} =
      volume T := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : {a : Fin r // a.val < j} => Fin (k + 1) → ℂ)
    (lowEquiv hj)).symm
  rw [← h.measure_preimage_equiv T]
  rfl

theorem card_UT (r : ℕ) : 2 * Fintype.card (UT r) ≤ r * (r - 1) := by
  have h : Fintype.card (UT r) = r.choose 2 := by
    rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
    simp
  rw [h, Nat.choose_two_right]
  exact Nat.mul_div_le _ _

theorem vol_box {k r j : ℕ} (β : Fin r → ℕ) (A : Set ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ))
    (B : Set ({p : UT r // p.1.1.val < j} → ℂ)) (C : Set ({a : Fin r // a.val < j} → ℝ)) (D : Set (UToff β → ℂ)) :
    (volume : Measure (PSec k r j × (UToff β → ℂ))) ((A ×ˢ B ×ˢ C) ×ˢ D) =
      volume A * (volume B * volume C) * volume D := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]

theorem sEl_mem {k r j : ℕ} (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : sEl k r j β q ∈ Nset k r :=
  isClosedSub_Nset.2.2.2.1 _ ((((Rad.radical k r).1 _ _).2.2.2 (Rad.skewM_skew _ _)).1) _ (UEmb.upper_mem _)

theorem ae_mem_range {k r j : ℕ} (β : Fin r → ℕ) {S : Set (Mat k r)} (hS : IsClosed S)
    (h : Set.range (rEl k r j β) ⊆ S) : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ S := by
  unfold lebR0
  have hS' : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  by_cases hm : AEMeasurable (fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r))
      (volume : Measure ((UTin β → ℂ) × PTop k r j))
  · rw [ae_map_iff hm hS'.measurableSet]
    exact Filter.Eventually.of_forall fun q => h ⟨q, rfl⟩
  · rw [Measure.map_of_not_aemeasurable hm]; simp

theorem N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_N {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {n x : Mat k r}
    (hn : n ∈ Nset k r) (hx : x ∈ GG k r) : Sg2 k r z (n * x) = Sg2 k r z x := by
  have := (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 x hx n (N_sub_S z hn) 1
    ⟨isClosedSub_GG.2.2.1, (Matrix.unitaryGroup _ ℂ).one_mem⟩
  rwa [Matrix.mul_one] at this

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  intro k r j hj z z' g₀ β c hz hz' hT hN h1j hjk De hDe m hm a ha
  have hT' : 0 < Tz k r z' := by rw [(GlobalTheory.Amp.NfMid.normal0_middle k r j hj z z' g₀ β c hz hz' hT hN).1]; exact hT
  obtain ⟨hR, hRc⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀ β c hz hz' hT hN
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm k r j hj z z' g₀ β c hz hz' hT hN m hm
  obtain ⟨hnull, hvol⟩ := GlobalTheory.Amp.GramVol.vol_gram k j h1j hjk m hm P₀ hP₀
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' g₀ hz hz' hT hT' hN.1
  have hsplit := GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section k r j β hN.2.2.2.1 hN.2.2.2.2.1
  have hB := fun R₀ hR₀ q => GlobalTheory.T.siegel_height_bound_section k r j hj z z' g₀ β c hz hz' hT hN De R₀ hDe hR₀ m hm q a ha
  have hY' := fun q => hY q a ha
  have hmul := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  have ht : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r := by
    refine hmul _ (UEmb.uEmb_mem _ ?_) _ (Rad.mEmb_mem m hm)
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = t at *
  have hae : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ Rset k r g₀ := ae_mem_range β hRc.2.1 hR.ge
  have hst : ∀ q : PSec k r j × (UToff β → ℂ), sEl k r j β q * t ∈ GG k r := fun q => hmul _ (sEl_mem β q).1 _ ht
  have hassoc : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r),
      (Matrix.of (rmulM t (rmulM (sEl k r j β q) ρ)) : Mat k r) = Matrix.of ρ * (sEl k r j β q * t) :=
    fun q ρ => by rw [of_rmulM, of_rmulM, Matrix.mul_assoc]
  have hYρ : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r), Matrix.of ρ ∈ Rset k r g₀ →
      Yj k r hj z z' g₀ (Matrix.of ρ * (sEl k r j β q * t)) =
        gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := fun q ρ hρ => by
    rw [(GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hN.1 _ (hst q)).2.2 _ hρ, hY' q]
  have htm : Measurable (rmulM t : Mt k r → Mt k r) := (continuous_rmulM t).measurable
  constructor
  · set S : Set (Mt k r) := {n | Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t n) = 0} with hS
    have hSm : MeasurableSet S := (hYm.comp htm) (measurableSet_singleton 0)
    refine measure_mono_null (t := S) (fun n hn => ?_) ?_
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    rw [← lintegral_indicator_one hSm, hsplit _ (measurable_one.indicator hSm)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    have h0 : (volume : Measure (PSec k r j × (UToff β → ℂ)))
        (({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0}} ×ˢ Set.univ ×ˢ Set.univ) ×ˢ Set.univ) = 0 := by
      rw [vol_box, vol_reindex hj, hnull, zero_mul, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hae] with ρ hρ
    refine Set.indicator_of_notMem (fun hmem => hq ⟨⟨?_, trivial, trivial⟩, trivial⟩) _
    have hG : rmulM t (rmulM (sEl k r j β q) ρ) ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
      rw [Set.mem_setOf_eq, hassoc]; exact hmul _ hρ.1.1 _ (hst q)
    have h2 : Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t (rmulM (sEl k r j β q) ρ)) = 0 := hmem
    rw [Set.indicator_of_mem hG, hassoc, hYρ q ρ hρ] at h2
    exact h2
  · intro φ hφ R₀ y hR₀ hy
    have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR₀) hDe.1
    have hB' := hB R₀ hR₀
    unfold fibVol0
    generalize R₀ ^ (2 * r) * De = M at *
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    rw [hsplit (fun n => φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM t n)) (hφ.1.mul ((measurable_one.indicator (hEm R₀ y)).comp htm))]
    set Box : Set (PSec k r j × (UToff β → ℂ)) :=
      ({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y}} ×ˢ
        {x | ∀ p, ‖x p‖ ≤ 2 * r * M ^ 2} ×ˢ {x | ∀ p, |x p| ≤ 2 * r * M ^ 2}) ×ˢ {x | ∀ p, ‖x p‖ ≤ M} with hBox
    refine (lintegral_mono (g := Box.indicator 1) fun q => ?_).trans ((lintegral_indicator_one_le Box).trans ?_)
    · by_cases hq : q ∈ Box
      · rw [Set.indicator_of_mem hq]
        refine le_trans (lintegral_mono fun ρ => ?_) (hφ.2 (Matrix.of.symm (sEl k r j β q)) (sEl_mem β q))
        exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le_one) _)
      · rw [Set.indicator_of_notMem hq]
        refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
        filter_upwards [hae] with ρ hρ
        refine mul_eq_zero_of_right _ (Set.indicator_of_notMem (fun hmem => hq ?_) _)
        obtain ⟨-, h1, h2, -, h3⟩ := hmem
        rw [hassoc] at h1 h2 h3
        rw [hYρ q ρ hρ] at h3
        rw [Sg2_N hz' hT' hρ.1 (hst q)] at h1
        have he : g₀ * (Matrix.of ρ * (sEl k r j β q * t)) =
            (g₀ * Matrix.of ρ * g₀⁻¹) * (g₀ * (sEl k r j β q * t)) := by
          rw [Matrix.mul_assoc (g₀ * Matrix.of ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hN.1),
            Matrix.mul_assoc]
        rw [he, Sg2_N hz hT hρ.2 (hmul _ hN.1 _ (hst q))] at h2
        obtain ⟨b1, b2, b3, b4⟩ := hB' q h1 (((TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.2 _).2.1.trans h2)
        exact ⟨⟨⟨fun b => b2 _, h3⟩, b3, b4⟩, b1⟩
    · have hr : (0 : ℝ) ≤ 2 * r * M ^ 2 := by positivity
      rw [hBox, vol_box, vol_reindex hj, vol_discs _ hr, vol_ints _ hr, vol_discs _ hM0]
      refine (mul_le_mul_left (mul_le_mul_left (hvol M y hM hy) _) _).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have har := box_volume_arith r j (Fintype.card (UToff β)) (Fintype.card {p : UT r // p.1.1.val < j})
        (Fintype.card {a : Fin r // a.val < j}) M h1j hj
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Fintype.card_subtype_le _).trans (Fintype.card_fin r).le) hM
      have hK : (0 : ℝ) ≤ (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j)) := by
        positivity
      refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right har hK).trans (le_of_eq ?_)) <;> ring

end GlobalTheory.Amp.FibreNormal
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  atlas_forward_decl GlobalTheory.Amp.FibreNormal.fibre_volume
end

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGramNumberNormalized_invariance : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  first | exact @GlobalTheory.Amp.YjInv.yj_invariant | exact GlobalTheory.Amp.YjInv.yj_invariant | (intros; apply GlobalTheory.Amp.YjInv.yj_invariant <;> assumption)
end

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_isotropic_flag : ∀ (k r : ℕ), ∀ g ∈ GG k r, ∃ n ∈ Nset k r, ∃ a : Fin r → ℝ, (∀ b, 0 < a b) ∧ ∃ m ∈ UH (Hb k), ∃ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), g = n * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m * κ := by
  first | exact @GlobalTheory.Amp.Iwa.iwasawa | exact GlobalTheory.Amp.Iwa.iwasawa | (intros; apply GlobalTheory.Amp.Iwa.iwasawa <;> assumption)
end

section
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolume

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_one : (1 : Mat k r) ∈ GG k r := (uHGroup _ _ hpk_unit).1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ _ hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨GG_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, n, hn, (one_mul n).symm⟩

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) :=
  Continuous.measurable (α := Mt k r) (γ := Mt k r) (continuous_two a b)

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have h1 : Measurable (lmulM a : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  have h2 : Measurable (rmulM b : Mt k r → Mt k r) := (continuous_rmulM b).measurable
  have : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [this, ← Measure.map_map h2 h1, hl, hr]

theorem Tz_eq {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {c : ℂ} (hg : g ∈ GG k r) (hc : ‖c‖ = 1)
    (h : g *ᵥ z' = c • z) : Tz k r z' = Tz k r z := by
  have h1 : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = herm (Hpk k r) z' z' := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
  have h2 : herm (Hpk k r) (c • z) (c • z) = herm (Hpk k r) z z := by
    have hcc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hc]; simp
    unfold herm
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, hcc, one_smul]
  unfold Tz
  rw [← h1, h, h2]

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  intro k r j hj z z' γ De s μR h1 h2 hDe hs hN g₁ hg₁
  obtain ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, rfl⟩ := hN
  obtain ⟨n₀, hn₀, a, ha, m, hm, κ, hκ, hg⟩ := GlobalTheory.T.iwasawa_decomposition_isotropic_flag k r g₁ hg₁
  have hT' : 0 < Tz k r z' := by rw [Tz_eq hg₀.1 hg₀.2.1 hg₀.2.2.1]; exact hT
  have hDe₀ : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl => ?_⟩
    have := hDe.2 l hl
    rwa [dInv k r z z' hz hz' n₁ (N_sub_S z hn₁) n₂ (N_sub_S z' hn₂)] at this
  have key := GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm k r j hj z z' g₀ β c hz hz' hT hg₀ h1 h2 De hDe₀ m hm a ha
  set A : Mat k r := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hg' : g₁ = n₀ * A * κ := by rw [hg, hA]; simp only [Matrix.mul_assoc]
  clear_value A
  have u₀ := GG_unit hn₀.1
  have u₂ := GG_unit hn₂.1
  have uκ := GG_unit hκ.1
  have hAG : A ∈ GG k r := by
    have : A = n₀⁻¹ * g₁ * κ⁻¹ := by
      rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₀, Matrix.one_mul,
        Matrix.mul_nonsing_inv_cancel_right _ _ uκ]
    rw [this]; exact GG_mul (GG_mul (GG_inv hn₀.1) hg₁) (GG_inv hκ.1)
  have hH := GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r
  have hU := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 hH).1
  set T := twoEquiv n₂ n₀ u₂ u₀ with hTdef
  have hmap : (lebN k r).map T = lebN k r := map_twoEquiv u₂ u₀ (hH.2.2.2 _ hn₂) (hU.1 _ hn₀)
  have hae : ∀ᵐ n ∂(lebN k r), Matrix.of n ∈ Nset k r := hH.2.2.1
  have hTof : ∀ n, (Matrix.of (T n) : Mat k r) = n₂ * Matrix.of n * n₀ := fun n => rfl
  have hγ : n₁ * g₀ * n₂ ∈ GG k r := GG_mul (GG_mul hn₁.1 hg₀.1) hn₂.1
  have hY : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
      Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = Yj k r hj z z' g₀ (Matrix.of (T n) * A) := by
    intro n hn
    rw [(GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _ (GG_mul hn.1 hg₁)).2.1 n₁ hn₁ n₂ hn₂, hTof,
      ← (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _
        (GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG)).1 κ hκ, hg']
    simp only [Matrix.mul_assoc]
  refine ⟨?_, fun φ hφ R₀ y hR hy => ?_⟩
  · have h0 := key.1
    rw [← hmap, MeasurableEquiv.map_apply] at h0
    rw [← h0]
    apply measure_congr
    filter_upwards [hae] with n hn
    show (Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0) = (Yj k r hj z z' g₀ (Matrix.of (T n) * A) = 0)
    rw [hY n hn]
  · have hE : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
        (rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y ↔ rmulM A (T n) ∈ Eset0 k r hj z z' g₀ R₀ y) := by
      intro n hn
      have hx : Matrix.of (T n) * A ∈ GG k r := GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG
      have e1 : Sg2 k r z' (Matrix.of n * g₁) = Sg2 k r z' (Matrix.of (T n) * A) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.1 _ hx n₂⁻¹ (N_sub_S z' ((nSubgroup k r).2.2 _ hn₂)) κ hκ, hTof, hg']
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul]
      have e2 : Sg2 k r z (n₁ * g₀ * n₂ * (Matrix.of n * g₁)) = Sg2 k r z (g₀ * (Matrix.of (T n) * A)) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 _ (GG_mul hg₀.1 hx) n₁ (N_sub_S z hn₁) κ hκ, hTof, hg']
        simp only [Matrix.mul_assoc]
      simp only [Eset0, Set.mem_setOf_eq, of_rmulM]
      rw [e1, e2, hY n hn]
      exact and_congr_left fun _ => iff_of_true (GG_mul hn.1 hg₁) hx
    set ψ : Mt k r → ℝ≥0∞ := fun x =>
      ENNReal.ofReal s * φ (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) with hψ
    have hψT : ∀ n, ψ (T n) = ENNReal.ofReal s * φ (rmulM g₁ n) := by
      intro n
      have : n₂⁻¹ * Matrix.of (T n) * (n₀⁻¹ * g₁) = Matrix.of n * g₁ := by
        rw [hTof]
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul,
          Matrix.mul_nonsing_inv_cancel_right _ _ u₀]
      simp only [hψ, this]; rfl
    have hsub : SubCut (Nset k r) (lebR0 k r j β) ψ := by
      refine ⟨(hφ.1.comp (measurable_two _ _)).const_mul _, fun x hx => ?_⟩
      have hw : n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁) ∈ GG k r :=
        GG_mul (GG_mul (GG_inv hn₂.1) hx.1) (GG_mul (GG_inv hn₀.1) hg₁)
      have h := hφ.2 (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) hw
      have hc : (conjM n₂⁻¹ : Mt k r → Mt k r) =
          twoEquiv n₂⁻¹ n₂⁻¹⁻¹ (GG_unit (GG_inv hn₂.1)) (GG_unit (GG_inv (GG_inv hn₂.1))) := rfl
      rw [hc, lintegral_map_equiv, lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
      refine le_of_eq_of_le (lintegral_congr fun ρ => ?_) h
      have : n₂⁻¹ * (Matrix.of ρ * Matrix.of x) * (n₀⁻¹ * g₁) =
          n₂⁻¹ * Matrix.of ρ * n₂⁻¹⁻¹ * (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁)) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ u₂]
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u₂]
      exact congrArg (fun w : Mat k r => ENNReal.ofReal s * φ (Matrix.of.symm w)) this
    have h := key.2 ψ hsub R₀ y hR hy
    rw [← hmap, lintegral_map_equiv] at h
    have h' : ENNReal.ofReal s * ∫⁻ n, φ (rmulM g₁ n) *
        (Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤
        ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) h
      filter_upwards [hae] with n hn
      rw [hψT, ← mul_assoc]
      refine congrArg (fun t => ENNReal.ofReal s * φ (rmulM g₁ n) * t) ?_
      by_cases hm : rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hE n hn).1 hm)]; rfl
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm ((hE n hn).2 h))]
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h'

end GlobalTheory.Amp.FibreVolume
end
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreVolume_normalFormStabiliser : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  atlas_forward_decl GlobalTheory.Amp.FibreVolume.fibre_volume
end

section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_computes_besselQuotientIntegral : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  first | exact @GlobalTheory.Amp.CutQuot.cut_quotient | exact GlobalTheory.Amp.CutQuot.cut_quotient | (intros; apply GlobalTheory.Amp.CutQuot.cut_quotient <;> assumption)
end

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegSide

variable {k r : ℕ}

theorem measurableSet_GG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  simpa [Set.compl_setOf] using (WUnfold.measurableSet_not_GG (k := k) (r := r)).compl

theorem measurable_indicator_GG {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {f : Mat k r → β} (hf : ContinuousOn f (GG k r)) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => f (Matrix.of x)) := by
  classical
  have h : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := h.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const measurableSet_GG
  rwa [← Set.piecewise_eq_indicator]

theorem measurable_mulP : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  have : Continuous fun p : Mat k r × Mat k r => p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  have h : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := this
  exact h.measurable

theorem measurable_conjM (h : Mat k r) : Measurable (conjM h : Mt k r → Mt k r) := by
  have : Continuous fun x : Mat k r => h * x * h⁻¹ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h' : Continuous (conjM h : Mt k r → Mt k r) := this
  exact h'.measurable

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muProd μW μN) ν)
    {A : Set (Mt k r)} (hA : MeasurableSet A) (h0 : ∀ g : Mat k r, μN (rmulM g ⁻¹' A) = 0) : μG A = 0 := by
  haveI := hN.1
  have hconj : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
    (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN).2.2.2.2
  have hm : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, hq _ hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  have hx : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  show ∫⁻ s, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) ∂(muProd μW μN) = 0
  unfold muProd
  rw [lintegral_map hx measurable_mulP, lintegral_prod (fun p : Mt k r × Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of p.1) p.2)))
      (hx.comp measurable_mulP).aemeasurable]
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := hW.2.2.1
  refine (lintegral_congr_ae (haeW.mono fun h hh => ?_)).trans lintegral_zero
  have hg : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  have e : ∀ n : Mt k r, rmulM (Matrix.of x) (lmulM (Matrix.of h) n) =
      rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
    intro n
    show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
      Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
    rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n : Mat k r),
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
  show ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN = 0
  simp only [e]
  rw [← lintegral_map hg (measurable_conjM _), hconj _ hh, ← h0 (Matrix.of h * Matrix.of x),
    ← lintegral_indicator_one ((continuous_rmulM _).measurable hA)]
  rfl

theorem mem_Sset_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {s x : Mat k r}
    (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : Sg2 k r z (s * x) = Sg2 k r z x := by
  have := (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩
  rwa [Matrix.mul_one] at this

theorem tail {Wq : Type} [NormedAddCommGroup Wq] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {ν : Measure (Mt k r)} {Φ : Mat k r → Wq} {q : ℕ} {H₁ : ℝ} (hH : 1 ≤ H₁) (ht : TailBd z ν Φ q H₁) (i : ℕ)
    {Q : Set (Mt k r)} (hQ : MeasurableSet Q) (hsub : ∀ x ∈ Q, i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z (Matrix.of x)) :
    ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG ν Φ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (setLIntegral_le_lintegral _ _).trans (le_mul_of_one_le_left zero_le ?_)
    rw [ENNReal.one_le_ofReal]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one]
    linarith
  · have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have h := ht (2 ^ i) h2
    have e : 2 * (2 * r + 2 : ℝ) * (2 ^ i : ℝ) ^ (-(2 * (q : ℝ))) = (4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹ := by
      rw [Real.rpow_neg h2.le, ← Real.rpow_natCast (2 ^ i : ℝ) (2 * q)]
      push_cast
      ring
    rw [e] at h
    refine le_trans ?_ h
    rw [← lintegral_indicator hQ]
    refine lintegral_mono (Set.indicator_le_indicator_of_subset (fun x hx => ?_) fun _ => zero_le)
    have hx' := (hsub x hx).resolve_left hi.ne'
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    rcases ((GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.2.2 (Matrix.of x)).2.2.2 with h' | ⟨a, ha⟩
    · exfalso
      rw [h'] at hx'
      nlinarith
    · exact ⟨a, ha ▸ hx'.le⟩

theorem side_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r j hj z z' Wq _ _ _ π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hjk hκ hs hH hO ht hDe hNR hqR
  have hO' := hO
  obtain ⟨hz', hT', hnt, hπ, -, hG, hW, -, hN, hqS, hψ, hΦ, hΦc, hc, hl2⟩ := hO'
  have hz := hNR.1
  have hT := hNR.2.2.1
  obtain ⟨hγ, hRc, hRh, hRu, -⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs hNR
  obtain ⟨hoff, hnull, φ, hφ, hcut⟩ := GlobalTheory.T.cutoff_computes_besselQuotientIntegral k r _ μG μR νR hRc hG hRh hRu hqR
  have hV := GlobalTheory.T.fibreVolume_normalFormStabiliser k r j hj z z' γ De s μR hj1 hjk hDe hs hNR
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ hz hz' hT hT' hγ
  have hYi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x :=
    fun ρ hρ x hx => (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' γ hz hz' hγ x hx).2.2 ρ hρ
  have hmul : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := isClosedSub_GG.2.2.2.1
  refine ⟨?_, fun w hw i R₀ y hR hy => ?_⟩
  · set A : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) = 0} with hAdef
    have hA : MeasurableSet A := by
      have := measurableSet_GG.inter (hYm (measurableSet_singleton 0))
      convert this using 1
      ext x
      refine and_congr_right fun hx => ?_
      rw [Set.mem_preimage, Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
      rfl
    have hA0 : μG A = 0 := by
      refine null_of_fibres hz' hT' hW hN hqS hA fun g => ?_
      by_cases hg : g ∈ GG k r
      · rw [Measure.smul_apply, measure_mono_null (t := {n | Yj k r hj z z' γ (Matrix.of n * g) = 0}) (fun n hn => hn.2)
          (hV g hg).1, smul_zero]
      · refine measure_mono_null (t := {x | Matrix.of x ∉ Nset k r}) (fun n hn hn' => hg ?_) hN.2.2.1
        exact (WUnfold.mul_mem_GG_iff hn'.1).1 hn.1
    have hA1 : νR A = 0 := by
      refine hnull A hA (fun ρ hρ x hx => ?_) hA0
      show (ρ * Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (ρ * Matrix.of x) = 0) ↔ (_ ∧ _)
      rw [hYi ρ hρ _ hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hoff hA1)
    by_cases hx' : Matrix.of x ∈ GG k r
    · exact Or.inr ⟨hx', hx.resolve_left (not_not.2 hx')⟩
    · exact Or.inl hx'
  · set E := Eset0 k r hj z z' γ R₀ y with hE
    set Q : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x))} with hQdef
    have hQ : MeasurableSet Q := by
      have h1 := measurable_indicator_GG (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.2.1
      have h2 := measurableSet_GG.inter ((MeasurableSet.const (i = 0)).union (measurableSet_lt
        (measurable_const (a := 2 ^ i * H₁)) h1))
      convert h2 using 1
      ext x
      refine and_congr_right fun hx => ?_
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
    have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)} = E ∩ Q := by
      ext x
      exact and_congr_right fun hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    have hQi : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
      intro s hs x hx
      show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (s * Matrix.of x))) ↔ (_ ∧ _)
      rw [Sg2_left hz' hT' hs hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ (WUnfold.Sset_subset _ hs) _ hx, h.2⟩⟩
    have hEi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ E ↔ x ∈ E) := by
      intro ρ hρ x hx
      show (ρ * Matrix.of x ∈ GG k r ∧ Sg2 k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
        y < Yj k r hj z z' γ (ρ * Matrix.of x) ∧ Yj k r hj z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔ (_ ∧ _)
      have e : γ * (ρ * Matrix.of x) = γ * ρ * γ⁻¹ * (γ * Matrix.of x) := by
        rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
      rw [hYi ρ hρ _ hx, Sg2_left hz' hT' (mem_Sset_of_mem_Nset _ hρ.1) hx, e,
        Sg2_left hz hT (mem_Sset_of_mem_Nset _ hρ.2) (hmul _ hγ _ hx)]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    set g : Mt k r → ℝ≥0∞ := fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with hg
    have hgi : ∀ ρ ∈ Nset k r, ∀ x, Matrix.of x ∈ GG k r → g (lmulM ρ x) = g x := by
      intro ρ hρ x hx
      have h1 := hΦ 1 (isClosedSub_UWset z').2.2.1 ρ hρ _ hx
      rw [Matrix.one_mul, hπ.1.1] at h1
      have h2 : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h1, inner_smul_right, nnnorm_mul, h2, one_mul]
      rfl
    have hFm : Measurable ((E ∩ Q).indicator g) := by
      have h1 : ContinuousOn (fun x : Mat k r => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) (GG k r) :=
        (ENNReal.continuous_pow 2).comp_continuousOn
          (ENNReal.continuous_coe.comp_continuousOn (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const hΦc).nnnorm)
      have h2 := (measurable_indicator_GG h1).indicator ((hEm R₀ y).inter hQ)
      rwa [Set.indicator_indicator, Set.inter_eq_left.2 (fun x hx => hx.2.1)] at h2
    have hFi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
        (E ∩ Q).indicator g (lmulM ρ x) = (E ∩ Q).indicator g x := by
      intro ρ hρ x hx
      have hiff : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
        and_congr (hEi ρ hρ x hx) (hQi ρ (mem_Sset_of_mem_Nset _ hρ.1) x hx)
      by_cases h : x ∈ E ∩ Q
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgi ρ hρ.1 x hx]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
    have hP := GlobalTheory.T.amplitude_one_side_unfolding k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
      (ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s))
      (hφ.1.mul (measurable_one.indicator (hEm R₀ y))) hQ hQi (fun g hg => by
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_right ((hV g hg).2 φ hφ R₀ y hR hy) _) w hw
    have hTl := tail hz' hT' hH ht i hQ fun x hx => hx.2
    have hfib : 0 ≤ fibVol0 k r j R₀ De y := by
      have := hDe.1
      unfold fibVol0
      positivity
    have hd : (0 : ℝ) < Module.finrank ℂ Wq := Nat.cast_pos.2 Module.finrank_pos
    calc ∫⁻ x in E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)},
          ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
        = ∫⁻ x, (E ∩ Q).indicator g x ∂νR := by
          rw [hEQ, lintegral_indicator ((hEm R₀ y).inter hQ)]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          rfl
      _ = ∫⁻ x in Q, φ x * E.indicator 1 x * g x ∂μG := by
          rw [hcut _ hFm hFi, ← lintegral_indicator hQ]
          refine lintegral_congr fun x => ?_
          by_cases h1 : x ∈ E <;> by_cases h2 : x ∈ Q <;> simp [h1, h2]
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s) * (Module.finrank ℂ Wq : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS' Φ') :=
          hP.trans (mul_le_mul_right hTl _)
      _ = _ := by
          rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp

end GlobalTheory.Amp.DegSide
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplification_degenerate_side_piece_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  atlas_forward_decl GlobalTheory.Amp.DegSide.side_bound
end
