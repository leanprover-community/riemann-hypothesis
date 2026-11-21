import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetLogNormDens
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace FubiniStudyLogRegularization

variable {n : ℕ}

def sqDual (h : HermNorm n) (y : Fin n → ℂ) : ℝ := ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2

def regMat (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  Matrix.of (Fin.cons u fun i => ((√ε : ℝ) : ℂ) • (h.matᵀ)⁻¹ i)

theorem sqDual_nonneg (h : HermNorm n) (y : Fin n → ℂ) : 0 ≤ sqDual h y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem dualNorm_sq (h : HermNorm n) (y : Fin n → ℂ) : h.dualNorm y ^ 2 = sqDual h y :=
  Real.sq_sqrt (sqDual_nonneg h y)

theorem sqDual_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < sqDual h y := by
  rw [← dualNorm_sq]
  exact pow_pos (h.dualNorm_pos hy) 2

theorem fsLogReg_eq (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) :
    fsLogReg h u ε y = Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 := by
  rw [fsLogReg, dualNorm_sq]

theorem contDiff_sqDual (h : HermNorm n) : ContDiff ℝ ∞ (sqDual h) := by
  unfold sqDual
  refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem contDiff_lin (u : Fin n → ℂ) : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))

theorem contDiffOn_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {x | x ≠ 0} := by
  intro y hy
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  have hD : ContDiffAt ℝ ∞ (fun y => (‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) y :=
    (((contDiff_lin u).add (contDiff_const.mul (contDiff_sqDual h))).contDiffAt).div
      (contDiff_sqDual h).contDiffAt hS.ne'
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((hD.log (div_pos hN hS).ne').div_const 2).contDiffWithinAt

theorem fsLogReg_smul (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {t : ℂ} (ht : t ≠ 0)
    (y : Fin n → ℂ) : fsLogReg h u ε (t • y) = fsLogReg h u ε y := by
  have hu : ‖∑ j, u j * (t • y) j‖ = ‖t‖ * ‖∑ j, u j * y j‖ := by
    rw [← norm_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hu, h.dualNorm_smul, mul_pow, mul_pow, ← mul_assoc, mul_comm ε, mul_assoc, ← mul_add,
    mul_div_mul_left _ _ ht2]

theorem fsLogReg_mono (h : HermNorm n) (u : Fin n → ℂ) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (y : Fin n → ℂ) : fsLogReg h u δ y ≤ fsLogReg h u δ' y := by
  rw [fsLogReg_eq, fsLogReg_eq]
  rcases (sqDual_nonneg h y).eq_or_lt with hS | hS
  · rw [← hS]
    simp
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have h1 : 0 < (‖∑ j, u j * y j‖ ^ 2 + δ * sqDual h y) / sqDual h y := by positivity
  have h2 : (‖∑ j, u j * y j‖ ^ 2 + δ * sqDual h y) / sqDual h y ≤
      (‖∑ j, u j * y j‖ ^ 2 + δ' * sqDual h y) / sqDual h y :=
    div_le_div_of_nonneg_right (by nlinarith) hS.le
  exact div_le_div_of_nonneg_right (Real.log_le_log h1 h2) zero_le_two

theorem measurable_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable (fsLogReg h u ε) := by
  have hf : fsLogReg h u ε = fun y =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 :=
    funext (fsLogReg_eq h u ε)
  rw [hf]
  exact ((Real.measurable_log.comp (((contDiff_lin u).continuous.measurable.add
    (measurable_const.mul (contDiff_sqDual h).continuous.measurable)).div
      (contDiff_sqDual h).continuous.measurable)).div_const 2)

theorem sum_regMat (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (y : Fin n → ℂ) :
    ∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2 = ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by
  have h0 : (regMat h u ε *ᵥ y) 0 = ∑ j, u j * y j := by
    simp [regMat, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ, sqDual, Finset.mul_sum, h0, add_right_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (regMat h u ε *ᵥ y) i.succ = ((√ε : ℝ) : ℂ) * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    simp only [regMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.cons_succ, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]

theorem regMat_mulVec_ne_zero (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℂ}
    (hy : y ≠ 0) : regMat h u ε *ᵥ y ≠ 0 := by
  intro h0
  have hs := sum_regMat h u hε.le y
  rw [h0] at hs
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hs
  nlinarith

theorem log_dualNorm_eq (h : HermNorm n) (y : Fin n → ℂ) :
    Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h 0 1 *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h 0 zero_le_one]
  simp [HermNorm.dualNorm, sqDual]

theorem fsLogReg_add_log (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℂ) :
    fsLogReg h u ε y + Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2) := by
  rw [sum_regMat h u hε.le, fsLogReg_eq]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [HermNorm.dualNorm, sqDual]
  have hS := sqDual_pos h hy
  have hQ : 0 ≤ ‖∑ j, u j * y j‖ ^ 2 := sq_nonneg _
  have hN : 0 < ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by positivity
  rw [Real.log_div hN.ne' hS.ne', Real.log_sqrt hN.le, HermNorm.dualNorm,
    show ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 = sqDual h y from rfl, Real.log_sqrt hS.le]
  ring

end FubiniStudyLogRegularization

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

theorem maDens_cons_add {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    maDens (fun k => vecCons (fun z => f z + g z) φ k ∘ s) (A *ᵥ x) =
      maDens (fun k => vecCons f φ k ∘ s) (A *ᵥ x) + maDens (fun k => vecCons g φ k ∘ s) (A *ᵥ x) := by
  have hsx : s (A *ᵥ x) = x := by
    obtain ⟨_, _, _, _, h, _⟩ := hs
    exact h
  have hS : ContDiffAt ℝ 2 s (A *ᵥ x) := (analyticAt_sheet hs).restrictScalars.contDiffAt
  have hf' : ContDiffAt ℝ 2 (f ∘ s) (A *ᵥ x) := (hsx ▸ hf).comp _ hS
  have hg' : ContDiffAt ℝ 2 (g ∘ s) (A *ᵥ x) := (hsx ▸ hg).comp _ hS
  have hadd : hessC ((fun z => f z + g z) ∘ s) (A *ᵥ x) =
      hessC (f ∘ s) (A *ᵥ x) + hessC (g ∘ s) (A *ᵥ x) :=
    ReciprocityTheory.AnForm.A.hessC_add (f ∘ s) (g ∘ s) _ hf' hg'
  have key : ∀ F : (Fin n → ℂ) → ℝ, (fun k => hessC (vecCons F φ k ∘ s) (A *ᵥ x)) =
      Function.update (fun k => hessC (vecCons f φ k ∘ s) (A *ᵥ x)) 0 (hessC (F ∘ s) (A *ᵥ x)) := by
    intro F
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp
    · simp
  simp only [maDens]
  rw [key (fun z => f z + g z), key g, hadd, ReciprocityTheory.AnForm.A.mdisc_update_add, ← key f, Complex.add_re,
    mul_add]

theorem dens_sum_nonneg (hD : SheetLogNormDens.Statement) (h : HermNorm n) (u' : Fin n → ℂ) {ε : ℝ}
    (hε : 0 < ε) {e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin (e + 1) → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (hx : x ≠ 0) :
    0 ≤ maDens (fun k => vecCons (fsLogReg h u' ε) (fun _ z => Real.log (h.dualNorm z)) k ∘ s) (A *ᵥ x) +
      maDens (fun k => (fun (_ : Fin (e + 1)) z => Real.log (h.dualNorm z)) k ∘ s) (A *ᵥ x) := by
  have hO : IsOpen {z : Fin n → ℂ | z ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hL : ContDiffAt ℝ 2 (fun z => Real.log (h.dualNorm z)) x :=
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hb : ContDiffAt ℝ 2 (fsLogReg h u' ε) x :=
    ((FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε).contDiffAt (hO.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hΨ : (fun (_ : Fin (e + 1)) z => Real.log (h.dualNorm z)) =
      vecCons (fun z => Real.log (h.dualNorm z)) (fun _ z => Real.log (h.dualNorm z)) := by
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
  rw [hΨ, ← maDens_cons_add hs _ _ _ hb hL]
  let T : Fin (e + 1) → Matrix (Fin (n + 1)) (Fin n) ℂ :=
    vecCons (FubiniStudyLogRegularization.regMat h u' ε) fun _ => FubiniStudyLogRegularization.regMat h 0 1
  have hpot : (fun k => vecCons (fun z => fsLogReg h u' ε z + Real.log (h.dualNorm z))
      (fun _ z => Real.log (h.dualNorm z)) k ∘ s) =
      fun k => (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s := by
    funext k y
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp only [Function.comp_apply, cons_val_zero, T]
      exact FubiniStudyLogRegularization.fsLogReg_add_log h u' hε _
    · simp only [Function.comp_apply, cons_val_succ, T]
      exact FubiniStudyLogRegularization.log_dualNorm_eq h _
  rw [hpot]
  refine hD n (e + 1) (n + 1) J A x s T hs fun k => ?_
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · exact FubiniStudyLogRegularization.regMat_mulVec_ne_zero h u' hε hx
  · exact FubiniStudyLogRegularization.regMat_mulVec_ne_zero h 0 one_pos hx

end FormIntegralPositivity

open FormIntegralPositivity in

theorem FormIntPos.proof (hC : ConeToProjective.Statement) (hM : SliceFormMass.Statement)
    (hD : SheetLogNormDens.Statement) : FormIntPos.Statement := by
  intro n e h W u u' ε δ δ' hW hF hε hδ hδδ'
  obtain ⟨F, hF⟩ := hF
  obtain ⟨j, hj⟩ := hW.isRelevant
  have hℓ : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W := ⟨Pi.single j 1, by rwa [linForm_single]⟩
  have hℓW : linForm hℓ.choose ∉ W := hℓ.choose_spec
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hform : ∀ a b, formInt h W e a b = varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) a
      (vecCons b fun _ x => Real.log (h.dualNorm x)) := by
    intro a b
    rw [formInt, dif_pos hℓ]
  have hcone : ∀ δ₀, 0 < δ₀ → coneIntegral h W (e + 1) (fsLogReg h u δ₀) =
      varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) (fsLogReg h u δ₀)
        (fun _ x => Real.log (h.dualNorm x)) := fun δ₀ hδ₀ =>
    hC n (e + 1) h W F hℓ.choose (fsLogReg h u δ₀) hW hF hℓW
      (fun t x ht => FubiniStudyLogRegularization.fsLogReg_smul h u δ₀ ht x)
      (FubiniStudyLogRegularization.contDiffOn_fsLogReg h u hδ₀).continuousOn
  rw [hform, hform, hcone δ hδ, hcone δ' hδ']
  unfold varInt
  split_ifs with hA
  swap
  · simp
  have hAfin := hA.choose_spec
  unfold chartInt

  have hint : ∀ δ₀, 0 < δ₀ → ∀ (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
      (∀ k (t : ℂ) x, t ≠ 0 → ψ k (t • x) = ψ k x) → (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose (fsLogReg h u δ₀)
        fun k x => c k * Real.log (h.dualNorm x) + ψ k x) := by
    intro δ₀ hδ₀ c ψ hψ hψs
    refine Integrable.mono' (hM n e h W F hℓ.choose hA.choose (fsLogReg h u δ₀) c ψ hW hF hℓW hAfin
      (fun t x ht => FubiniStudyLogRegularization.fsLogReg_smul h u δ₀ ht x)
      (FubiniStudyLogRegularization.contDiffOn_fsLogReg h u hδ₀).continuousOn hψ hψs) ?_
      (Eventually.of_forall fun y => ?_)
    · exact (SheetSumMeasurable.measurable_sheetSum hAfin (fun a b => a * b)
        (continuous_fst.mul continuous_snd).measurable (FubiniStudyLogRegularization.measurable_fsLogReg h u δ₀)
        _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_chartDens_le _ _ _ _ y
  have h1 : ∀ δ₀, 0 < δ₀ → Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose
      (fsLogReg h u δ₀) (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) := by
    intro δ₀ hδ₀
    have e1 : (fun (k : Fin (e + 1)) x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k *
        Real.log (h.dualNorm x) + (vecCons (fsLogReg h u' ε) fun _ _ => 0 :
          Fin (e + 1) → (Fin n → ℂ) → ℝ) k x) =
        vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) := by
      funext k x
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
    rw [← e1]
    refine hint δ₀ hδ₀ _ _ (fun k t x ht => ?_) fun k => ?_
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.fsLogReg_smul h u' ε ht x
      · rfl
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε
      · exact contDiffOn_const
  have h2 : ∀ δ₀, 0 < δ₀ → Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose
      (fsLogReg h u δ₀) fun _ x => Real.log (h.dualNorm x)) := by
    intro δ₀ hδ₀
    have := hint δ₀ hδ₀ (fun _ => 1) (fun _ _ => 0) (fun _ _ _ _ => rfl) fun _ => contDiffOn_const
    simpa using this
  rw [← integral_add (h1 δ hδ) (h2 δ hδ), ← integral_add (h1 δ' hδ') (h2 δ' hδ')]
  refine integral_mono ((h1 δ hδ).add (h2 δ hδ)) ((h1 δ' hδ').add (h2 δ' hδ')) fun y => ?_

  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
  simp only [chartDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp [linForm] at this
  split_ifs with hs
  · have hpos := dens_sum_nonneg hD h u' hε hs.choose_spec hx0
    have hmono := mul_le_mul_of_nonneg_right (FubiniStudyLogRegularization.fsLogReg_mono h u hδ hδδ' x) hpos
    linarith
  · simp

end

end GroundTheory.Heights₂.Heights
end
