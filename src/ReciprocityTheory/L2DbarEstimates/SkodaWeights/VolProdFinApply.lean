module

public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement
public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffAtComplex
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

section
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

lemma measurable_exp_neg_density {M : Type*} [MeasurableSpace M] {ψ : M → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := (hψ.neg.exp).ennreal_ofReal

lemma ae_weighted_iff_ae (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (P : M → Prop) :
    (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x := by
  unfold wvol
  rw [ae_withDensity_iff (measurable_exp_neg_density hψ)]
  refine ⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma weightedIntegral_eq_lintegral (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    wint n z f ψ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂wvol n z ψ := by
  unfold wint wvol
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_exp_neg_density hψ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.rpow_two,
    ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

lemma eLpNorm_two_weighted_eq (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm' f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm'_eq_lintegral_eNorm, ← weightedIntegral_eq_lintegral n z hψ f]

theorem l2w (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by
  intro z ψ hψ
  refine ⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩
  · have hlt := Lp.eLpNorm_lt_top F
    have hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (Lp.aestronglyMeasurable F),
        ENNReal.toReal_ofNat, eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    · rw [hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]
  · have hmem : MemLp f 2 (wvol n z ψ) := by
      change eLpNorm f 2 (wvol n z ψ) < ⊤
      have hfw : AEStronglyMeasurable f (wvol n z ψ) :=
        hf.mono_ac (withDensity_absolutelyContinuous _ _)
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfw, ENNReal.toReal_ofNat,
        eLpNorm_two_weighted_eq n z hψ f]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact ⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp
      (MemLp.coeFn_toLp hmem)⟩

theorem volOpenPos (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    VolOpenPosStatement n M := by
  intro z hz U hU ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hW : IsOpen (U ∩ e.source) := hU.inter e.open_source
  have hinj : Set.InjOn z e.source := by
    intro a ha b hb hab
    rw [he ha, he hb] at hab
    exact e.injOn ha hb hab
  have himg : z '' (U ∩ e.source) = e '' (U ∩ e.source) :=
    Set.image_congr fun y hy => he hy.2
  have hpos : 0 < volume (z '' (U ∩ e.source)) := by
    rw [himg]
    exact (e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _
      ⟨e x, x, ⟨hx, hxe⟩, rfl⟩
  rw [← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet
    Set.inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono Set.inter_subset_left)

end ReciprocityTheory.L2DbarEstimates.H
end
end


section
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff

theorem vsq_pos {p : ℕ} (w : Fin p → ℂ) (hw : w ≠ 0) : 0 < vsq w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := by simpa using hi
  have h1 : 0 < ‖w i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi') 2
  have h2 : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  exact lt_of_lt_of_le h1 h2

theorem smoothR_vsq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) {p : ℕ}
    (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l)) : SmoothR n z (fun x => vsq (gv g x)) := by
  unfold SmoothR Smooth
  intro e he
  have hd : ∀ l, ContDiffOn ℝ ∞ (fun y => g l (e.symm y)) e.target := by
    intro l
    have h1 : ContDiffOn ℝ ∞ (g l ∘ e.symm) e.target := Holo.smooth n z (g l) (hg l) e he
    exact h1
  have hs : ContDiffOn ℝ ∞ (fun y => ∑ l, ‖g l (e.symm y)‖ ^ 2) e.target :=
    ContDiffOn.sum (fun l _ => (contDiff_norm_sq ℂ).comp_contDiffOn (hd l))
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  simpa [Function.comp_def, vsq, gv] using h4

theorem smoothR_log (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f : M → ℝ)
    (hf : SmoothR n z f) (hpos : ∀ x, 0 < f x) : SmoothR n z (fun x => Real.log (f x)) := by
  unfold SmoothR Smooth at *
  intro e he
  have h1 := hf e he
  have h2 : ContDiffOn ℝ ∞ (fun y => f (e.symm y)) e.target := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn h1
    simpa [Function.comp_def] using h
  have h3 : ContDiffOn ℝ ∞ (fun y => Real.log (f (e.symm y))) e.target :=
    h2.log (fun y _ => (hpos _).ne')
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  simpa [Function.comp_def] using h4

private theorem eq_neg_mul_inv_sq_of_zero_eq (A B s : ℂ) (hs : s ≠ 0) (h : 0 = A * s⁻¹ + s * B) :
    B = -A * s⁻¹ ^ 2 := by
  have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  linear_combination (-(s⁻¹)) * h - B * hinv

theorem skodaDbar (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaDbarStatement n M := by
  unfold SkodaDbarStatement
  intro z hz p g u hg hu hg0 x i ξ
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
  have hus : Ck n z 1 u := Smooth.ck n z 1 _ (Holo.smooth n z _ hu)
  have hcg : ∀ l, Ck n z 1 (fun y => (starRingEnd ℂ) (g l y)) :=
    fun l => Ck.conj n z 1 _ (hgs l)
  have hS : ∀ y, ((vsq (gv g y) : ℝ) : ℂ) ≠ 0 :=
    fun y => Complex.ofReal_ne_zero.mpr (vsq_pos _ (hg0 y)).ne'
  have hSsm : Smooth n z (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := smoothR_vsq n z g hg
  have hSc : Ck n z 1 (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := Smooth.ck n z 1 _ hSsm
  have hSi : Ck n z 1 (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    apply Smooth.ck
    unfold Smooth
    intro e he
    exact (hSsm e he).inv (fun y _ => hS _)
  have hSfun : (fun y => ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => ∑ l, (starRingEnd ℂ) (g l y) * g l y := by
    funext y
    simp only [vsq, gv, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hdbS : ∀ j, db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x := by
    intro j
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) j x, db_conj, Holo.db_eq_zero n z _ (hg l) j x]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdbSi : ∀ j, db n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact db_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (db_mul n z _ _ hSc hSi j x))
  have hF : (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => u y * ((starRingEnd ℂ) (g i y) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    funext y
    rw [div_eq_mul_inv, mul_assoc]
  have hdbF : ∀ j, db n z j
      (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x =
      u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) := by
    intro j
    rw [hF, db_mul n z _ _ hus (Ck.mul n z 1 _ _ (hcg i) hSi) j x, Holo.db_eq_zero n z _ hu j x,
      db_mul n z _ _ (hcg i) hSi j x, db_conj, hdbSi j, hdbS j]
    try beta_reduce
    ring
  have hL : dbarDot n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x ξ =
      ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) := by
    unfold dbarDot
    exact Finset.sum_congr rfl (fun j _ => by rw [hdbF j])
  have hsplit : ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) =
      u x * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        u x * (starRingEnd ℂ) (g i x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
          ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hswap : ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) =
      ∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hconj : (starRingEnd ℂ) (perp (gv g x) (jacM n z g x ξ) i) =
      ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        (starRingEnd ℂ) (g i x) *
          (∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j)) /
            ((vsq (gv g x) : ℝ) : ℂ) := by

    simp only [perp, jacM, gv, map_sub, map_mul, map_sum, map_div₀, Complex.conj_ofReal,
    Complex.conj_conj]
    ring
  rw [hL, hsplit, hswap, hconj]
  ring

private theorem db_log_eq_inv_mul_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : Fin n) (ph : M → ℝ) (hph : SmoothR n z ph) (hpos : ∀ y, 0 < ph y) (y : M) :
    db n z k (fun y => ((Real.log (ph y) : ℝ) : ℂ)) y =
      ((ph y : ℝ) : ℂ)⁻¹ * db n z k (fun y => ((ph y : ℝ) : ℂ)) y := by
  unfold db
  by_cases hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source
  · rw [dite_eq_left hex, dite_eq_left hex]
    have hs := Classical.choose_spec hex
    generalize Classical.choose hex = e at hs ⊢
    have hzy : z y = e y := hs.1 hs.2
    have hp : e y ∈ e.target := e.map_source hs.2
    have hsy : e.symm (e y) = y := e.left_inv hs.2
    have hc : ContDiffOn ℝ ∞ (fun w => ph (e.symm w)) e.target := by
      have h := Complex.reCLM.contDiff.comp_contDiffOn (hph e hs.1)
      simpa [Function.comp_def] using h
    have hd : DifferentiableAt ℝ (fun w => ph (e.symm w)) (e y) :=
      (hc.differentiableOn (by first | simp)
        ).differentiableAt (e.open_target.mem_nhds hp)
    have hne : ph (e.symm (e y)) ≠ 0 := (hpos _).ne'
    have h1 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) (hd.hasFDerivAt.log hne)).fderiv
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) hd.hasFDerivAt).fderiv
    have hf1 : (fun y => ((Real.log (ph y) : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => Real.log (ph (e.symm w)) := by
      funext w
      simp
    have hf2 : (fun y => ((ph y : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => ph (e.symm w) := by
      funext w
      simp
    rw [hzy]
    unfold wdb
    rw [hf1, hf2, h1, h2, hsy]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  · rw [dite_eq_right hex, dite_eq_right hex, mul_zero]

private theorem ofReal_vsq_perp_eq {p : ℕ} (g w : Fin p → ℂ) (hS : vsq g ≠ 0) :
    ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, w l * (starRingEnd ℂ) (w l) -
      (∑ l, (starRingEnd ℂ) (g l) * w l) * (∑ l, g l * (starRingEnd ℂ) (w l)) / ((vsq g : ℝ) : ℂ) := by
  have hSc : ((vsq g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
  have hgg : ∑ l, (starRingEnd ℂ) (g l) * g l = ((vsq g : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e1 : ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (perp g w l) * perp g w l := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e2 : ∀ l, (starRingEnd ℂ) (perp g w l) * perp g w l =
      w l * (starRingEnd ℂ) (w l) -
      ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * (g l * (starRingEnd ℂ) (w l)) -
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * w l) +
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) *
        ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * g l) := by
    intro l

    simp only [perp, map_sub, map_mul, map_div₀, map_sum, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [e1, Finset.sum_congr rfl (fun l _ => e2 l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hgg]
  field_simp
  ring

private theorem levi_form_expand_eq_neg_sq_mul_add_sum {n p : ℕ} (a : Fin n → Fin p → ℂ) (G : Fin p → ℂ) (ξ : Fin n → ℂ)
    (c : ℂ) :
    ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (G l) * a j l) * c ^ 2 * (∑ l, (starRingEnd ℂ) (a k l) * G l) +
      c * ∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) =
    -(c ^ 2) * ((∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j) *
      (∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j))) +
    c * ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) := by
  have h1 : ∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j =
      ∑ j, (∑ l, (starRingEnd ℂ) (G l) * a j l) * ξ j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h2 : ∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * G l) * (starRingEnd ℂ) (ξ k) := by

    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h3 : ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ j, ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) := by

    simp only [map_sum, map_mul, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h1, h2, h3, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem skodaLevi (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaLeviStatement n M := by
  unfold SkodaLeviStatement
  intro z hz p g hg hg0 x ξ
  have hgs2 : ∀ l, Ck n z 2 (g l) := fun l => Smooth.ck n z 2 _ (Holo.smooth n z _ (hg l))
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
  have hcg : ∀ l, Ck n z 1 (fun y => (starRingEnd ℂ) (g l y)) :=
    fun l => Ck.conj n z 1 _ (hgs l)
  have hS : ∀ y, ((vsq (gv g y) : ℝ) : ℂ) ≠ 0 :=
    fun y => Complex.ofReal_ne_zero.mpr (vsq_pos _ (hg0 y)).ne'
  have hSsm : Smooth n z (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := smoothR_vsq n z g hg
  have hSc : Ck n z 1 (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := Smooth.ck n z 1 _ hSsm
  have hSi : Ck n z 1 (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    apply Smooth.ck
    unfold Smooth
    intro e he
    exact (hSsm e he).inv (fun y _ => hS _)
  have hSfun : (fun y => ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => ∑ l, (starRingEnd ℂ) (g l y) * g l y := by
    funext y
    simp only [vsq, gv, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hdbS : ∀ k y, db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) y =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k y
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) k y]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) k y, db_conj, Holo.db_eq_zero n z _ (hg l) k y]
    ring
  have hdS : ∀ j, d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x := by
    intro j
    rw [hSfun, d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (hcg l) (hgs l) j x, d_conj, Holo.db_eq_zero n z _ (hg l) j x, map_zero]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdSi : ∀ j, d n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact d_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (d_mul n z _ _ hSc hSi j x))
  have hE : ∀ k, Ck n z 1 (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) := by
    intro k
    have h : (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) =
        db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := funext (fun y => (hdbS k y).symm)
    rw [h]
    exact Smooth.ck n z 1 _ (Smooth.db n z k _ hSsm)
  have hdg1 : ∀ k l, Ck n z 1 (d n z k (g l)) := fun k l => Ck.d n z 1 k (g l) (hgs2 l)
  have hdb0 : ∀ j l, db n z j (g l) = fun _ => 0 :=
    fun j l => funext (Holo.db_eq_zero n z _ (hg l) j)
  have hdEk : ∀ j k, d n z j (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (d n z k (g l) y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l) j x, d_conj,
      ← d_db_comm n z (g l) (hgs2 l) k j x, hdb0 j l, d_const, map_zero]
    ring
  have hdE : ∀ j k, d n z j
      (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      -(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
      ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_mul n z _ _ hSi (hE k) j x, hdSi j, hdS j, hdEk j k]
  have hG : ∀ k, db n z k (fun y => ((Real.log (vsq (gv g y)) : ℝ) : ℂ)) =
      fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k
    funext y
    rw [db_log_eq_inv_mul_db n z k _ (smoothR_vsq n z g hg) (fun y => vsq_pos _ (hg0 y)) y, hdbS k y]
  have hLevi : Levi n z (fun y => Real.log (vsq (gv g y))) x ξ =
      ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
        ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x) * ξ j * (starRingEnd ℂ) (ξ k) := by
    unfold Levi
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hG k, hdE j k]
  refine (hLevi.trans (levi_form_expand_eq_neg_sq_mul_add_sum (fun j l => d n z j (g l) x) (gv g x) ξ (((vsq (gv g x) : ℝ) : ℂ)⁻¹))).trans ?_
  rw [Complex.ofReal_div, ofReal_vsq_perp_eq (gv g x) (jacM n z g x ξ) (vsq_pos _ (hg0 x)).ne']
  simp only [jacM, gv]
  ring

theorem skodaWeight (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaWeightStatement n M := by
  unfold SkodaWeightStatement
  intro z hz p g φ₀ t hg hg0 hφ hL ht
  have hpos : ∀ x, 0 < vsq (gv g x) := fun x => vsq_pos _ (hg0 x)
  have hlog : SmoothR n z (fun x => Real.log (vsq (gv g x))) :=
    smoothR_log n z _ (smoothR_vsq n z g hg) hpos
  have hconst : SmoothR n z (fun _ : M => t) := by
    unfold SmoothR Smooth
    intro e _
    exact contDiffOn_const
  have htl : SmoothR n z (fun x => t * Real.log (vsq (gv g x))) :=
    SmoothR.mul n z _ _ hconst hlog
  have hsm : SmoothR n z (skW g φ₀ t) := SmoothR.add n z _ _ hφ htl
  have hlevi : ∀ x ξ, Levi n z (skW g φ₀ t) x ξ = Levi n z φ₀ x ξ +
      (t : ℂ) * ((vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x) : ℝ) : ℂ) := by
    intro x ξ
    have e1 := levi_add n z φ₀ (fun y => t * Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 φ₀ hφ) (SmoothR.ckR n z 2 _ htl) x ξ
    have e2 := levi_const_mul n z t (fun y => Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 _ hlog) x ξ
    have e3 := skodaLevi n M z hz p g hg hg0 x ξ
    rw [← e3, ← e2]
    exact e1
  have hre : ∀ x ξ, (Levi n z (skW g φ₀ t) x ξ).re =
      (Levi n z φ₀ x ξ).re + t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    rw [hlevi x ξ, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hq : ∀ x ξ, 0 ≤ t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    have h0 : 0 ≤ vsq (perp (gv g x) (jacM n z g x ξ)) := by
      unfold vsq
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_nonneg ht (div_nonneg h0 (hpos x).le)
  refine ⟨hsm, ?_, ?_⟩
  · unfold LeviNonneg
    intro x ξ
    rw [hre]
    exact add_nonneg (hL x ξ) (hq x ξ)
  · intro x ξ
    rw [hre]
    linarith [hL x ξ]

private theorem sum_conj_mul_perp_eq_zero {p : ℕ} (w a : Fin p → ℂ) (hw : vsq w ≠ 0) :
    ∑ j, (starRingEnd ℂ) (w j) * perp w a j = 0 := by
  have hs : ∑ j, (starRingEnd ℂ) (w j) * w j = ((vsq w : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hw' : ((vsq w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have h1 : ∑ j, (starRingEnd ℂ) (w j) * perp w a j =
      ∑ j, (starRingEnd ℂ) (w j) * a j - (∑ j, (starRingEnd ℂ) (w j) * w j) *
        ((∑ j, (starRingEnd ℂ) (w j) * a j) / ((vsq w : ℝ) : ℂ)) := by
    simp only [perp]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h1, hs, mul_div_cancel₀ _ hw', sub_self]

private theorem norm_perp_apply_sq_le {p : ℕ} (w a : Fin p → ℂ) (i : Fin p) (hw : w ≠ 0) :
    ‖perp w a i‖ ^ 2 ≤ (1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a) := by
  have hW : 0 < vsq w := vsq_pos w hw
  have horth := sum_conj_mul_perp_eq_zero w a hW.ne'
  have hsplit : (starRingEnd ℂ) (w i) * perp w a i +
      ∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j = 0 :=
    (Finset.add_sum_erase Finset.univ (fun j => (starRingEnd ℂ) (w j) * perp w a j)
      (Finset.mem_univ i)).trans horth
  have hneg : (starRingEnd ℂ) (w i) * perp w a i =
      -∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j := by
    linear_combination hsplit
  have hA : ‖w i‖ * ‖perp w a i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
    calc ‖w i‖ * ‖perp w a i‖ = ‖(starRingEnd ℂ) (w i) * perp w a i‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ = ‖∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j‖ := by
          rw [hneg, norm_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖(starRingEnd ℂ) (w j) * perp w a j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
          simp only [norm_mul, Complex.norm_conj]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) (fun j => ‖w j‖)
    (fun j => ‖perp w a j‖)
  have h0 : 0 ≤ ‖w i‖ * ‖perp w a i‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (‖w i‖ * ‖perp w a i‖) ^ 2 ≤ (∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2) *
      ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 := by
    nlinarith [mul_le_mul hA hA h0 (le_trans h0 hA), hCS]
  have hWs : ‖w i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2 = vsq w :=
    Finset.add_sum_erase Finset.univ (fun j => ‖w j‖ ^ 2) (Finset.mem_univ i)
  have hVs : ‖perp w a i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 =
      vsq (perp w a) :=
    Finset.add_sum_erase Finset.univ (fun j => ‖perp w a j‖ ^ 2) (Finset.mem_univ i)
  have h3 : vsq w * ‖perp w a i‖ ^ 2 ≤ (vsq w - ‖w i‖ ^ 2) * vsq (perp w a) := by
    rw [← hWs, ← hVs]
    nlinarith [h2]
  rw [one_sub_div hW.ne', div_mul_eq_mul_div, le_div_iff₀ hW]
  nlinarith [h3]

theorem skodaHyp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaHypStatement n M := by
  unfold SkodaHypStatement
  intro z hz p g φ₀ t u hg hu hg0 hφ hL ht x i ξ
  rw [skodaDbar n M z hz p g u hg hu hg0 x i ξ]
  have hW := (skodaWeight n M z hz p g φ₀ t hg hg0 hφ hL ht.le).2.2 x ξ
  rw [show g i x = gv g x i from rfl]
  generalize (Levi n z (skW g φ₀ t) x ξ).re = L at hW ⊢
  generalize jacM n z g x ξ = a at hW ⊢
  have hw0 := hg0 x
  generalize gv g x = w at hw0 hW ⊢
  have hWp : 0 < vsq w := vsq_pos w hw0
  have hWn : vsq w ≠ 0 := hWp.ne'
  have htn : t ≠ 0 := ht.ne'
  have hn : ‖((vsq w : ℝ) : ℂ)‖ = vsq w := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWp]
  have hLHS : ‖u x * (starRingEnd ℂ) (perp w a i) / ((vsq w : ℝ) : ℂ)‖ ^ 2 =
      ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_conj, hn]
    ring
  rw [hLHS]
  have key := norm_perp_apply_sq_le w a i hw0
  have hwi : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hc : 0 ≤ 1 - ‖w i‖ ^ 2 / vsq w := sub_nonneg.mpr ((div_le_one hWp).mpr hwi)
  have hU : 0 ≤ ‖u x‖ ^ 2 := by positivity
  calc ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2
      ≤ ‖u x‖ ^ 2 * ((1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a)) / vsq w ^ 2 := by
        gcongr
    _ = ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) *
          (t * (vsq (perp w a) / vsq w)) := by
        field_simp
    _ ≤ ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) * L :=
        mul_le_mul_of_nonneg_left hW (div_nonneg (mul_nonneg hU hc) (mul_pos ht hWp).le)

end ReciprocityTheory.L2DbarEstimates.H
end
end


section
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

def chartSlice {M : Type*} [TopologicalSpace M] {n : ℕ} (e : OpenPartialHomeomorph M (V n))
    {p : ℕ} (i : Fin p) : OpenPartialHomeomorph (M × Fin p) (V n) where
  toFun q := e q.1
  invFun y := (e.symm y, i)
  source := e.source ×ˢ {i}
  target := e.target
  map_source' _q hq := e.map_source hq.1
  map_target' _y hy := ⟨e.map_target hy, rfl⟩
  left_inv' _q hq := Prod.ext (e.left_inv hq.1) (Set.mem_singleton_iff.1 hq.2).symm
  right_inv' _y hy := e.right_inv hy
  open_source := e.open_source.prod (isOpen_discrete _)
  open_target := e.open_target
  continuousOn_toFun := e.continuousOn.comp continuousOn_fst (fun _q hq => hq.1)
  continuousOn_invFun := e.continuousOn_symm.prodMk continuousOn_const

theorem isChart_chartSlice {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (p : ℕ) (i : Fin p) :
    IsChart n (fun q : M × Fin p => z q.1) (chartSlice e i) := by
  intro q hq
  exact he hq.1

theorem isLocalHomeomorph_comp_fst {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    IsLocalHomeomorph (fun q : M × Fin p => z q.1) := by
  intro q
  obtain ⟨e, hx, he⟩ := hz q.1
  refine ⟨chartSlice e q.2, ⟨hx, rfl⟩, ?_⟩
  funext r
  rw [he]
  rfl

theorem chart_prodFin_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (E : OpenPartialHomeomorph (M × Fin p) (V n)) (hE : IsChart n (fun q : M × Fin p => z q.1) E)
    (y : V n) (hy : y ∈ E.target) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (i : Fin p), IsChart n z e ∧ y ∈ e.target ∧
      (E.symm : V n → M × Fin p) =ᶠ[𝓝 y] fun w => (e.symm w, i) := by
  set q := E.symm y with hq
  have hqs : q ∈ E.source := E.map_target hy
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz q.1
  have hcont : ContinuousAt E.symm y := E.continuousAt_symm hy
  have hzq : z q.1 = y := by
    have h1 : z q.1 = E q := hE hqs
    rw [h1]; exact E.right_inv hy
  refine ⟨e, q.2, he, ?_, ?_⟩
  · rw [← hzq, he hxe]; exact e.map_source hxe
  · have t1 : ∀ᶠ w in 𝓝 y, (E.symm w).1 ∈ e.source :=
      (continuous_fst.continuousAt.comp hcont).preimage_mem_nhds (e.open_source.mem_nhds hxe)
    have t2 : ∀ᶠ w in 𝓝 y, (E.symm w).2 = q.2 :=
      (continuous_snd.continuousAt.comp hcont).preimage_mem_nhds ((isOpen_discrete {q.2}).mem_nhds rfl)
    have t3 : ∀ᶠ w in 𝓝 y, w ∈ E.target := E.open_target.mem_nhds hy
    filter_upwards [t1, t2, t3] with w h1 h2 h3
    have hz1 : z (E.symm w).1 = w := by
      have h4 : z (E.symm w).1 = E (E.symm w) := hE (E.map_target h3)
      rw [h4, E.right_inv h3]
    refine Prod.ext ?_ h2
    calc (E.symm w).1 = e.symm (e (E.symm w).1) := (e.left_inv h1).symm
      _ = e.symm w := by rw [← he h1, hz1]

theorem smooth_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Smooth n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Smooth n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : ContDiffAt ℝ ∞ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).contDiffAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).contDiffWithinAt

theorem holo_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Holo n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Holo n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : DifferentiableAt ℂ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).differentiableAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).differentiableWithinAt

theorem db_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    db n (fun q : M × Fin p => z q.1) j F (x, i) = db n z j (fun y => F (y, i)) x := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [db_eq_wdb n _ (chartSlice e i) (isChart_chartSlice n z e he p i) j F (x, i) ⟨hx, rfl⟩,
    db_eq_wdb n z e he j _ x hx]
  rfl

theorem levi_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (ph : M × Fin p → ℝ) (x : M) (i : Fin p) (ξ : Fin n → ℂ) :
    Levi n (fun q : M × Fin p => z q.1) ph (x, i) ξ = Levi n z (fun y => ph (y, i)) x ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  rw [levi_eq_leviV n _ (chartSlice e i) (isChart_chartSlice n z e he p i) ph (x, i) ⟨hx, rfl⟩ ξ,
    levi_eq_leviV n z e he _ x hx ξ]
  rfl

theorem volFun_prod_singleton {M : Type*} (n : ℕ) (z : M → V n) (p : ℕ) (B : Set M) (i : Fin p) :
    volFun n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = volFun n z B := by
  unfold volFun
  refine lintegral_congr fun y => ?_
  have h : (B ×ˢ {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} = (fun x => (x, i)) '' (B ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨x', ⟨hx, hy⟩, rfl, rfl⟩
      exact ⟨⟨hx, rfl⟩, hy⟩
  rw [h, (Prod.mk_left_injective i).encard_image]

theorem vol_prodFin_eq {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i, (vol n z).map (fun x => (x, i)) := by
  ext A hA
  have hz' := isLocalHomeomorph_comp_fst n z hz p
  have hS : ∀ i : Fin p, MeasurableSet ((fun x => (x, i)) ⁻¹' A) := fun i =>
    (measurable_id.prodMk measurable_const) hA
  have hA' : A = ⋃ i : Fin p, ((fun x => (x, i)) ⁻¹' A) ×ˢ {i} := by
    ext ⟨x, j⟩
    simp
  rw [MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply]
  conv_lhs => rw [hA']
  rw [measure_iUnion (by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro q hqi hqj
      rcases q with ⟨x, k⟩
      change x ∈ (fun x => (x, i)) ⁻¹' A ∧ k ∈ ({i} : Set (Fin p)) at hqi
      change x ∈ (fun x => (x, j)) ⁻¹' A ∧ k ∈ ({j} : Set (Fin p)) at hqj
      exact hij ((Set.mem_singleton_iff.mp hqi.2).symm.trans (Set.mem_singleton_iff.mp hqj.2)))
    (fun i => (hS i).prod (measurableSet_singleton i)), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (f := fun x => (x, i)) (measurable_id.prodMk measurable_const) hA,
    vol_apply n _ hz' _ ((hS i).prod (measurableSet_singleton i)), volFun_prod_singleton,
    vol_apply n z hz _ (hS i)]

theorem lintegral_vol_prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫⁻ x, f (x, i) ∂vol n z := by
  rw [vol_prodFin_eq n z hz p, MeasureTheory.lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_map hf (measurable_id.prodMk measurable_const)

def EtaleStein.prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (X : EtaleStein n M) (p : ℕ) :
    EtaleStein n (M × Fin p) where
  z q := X.z q.1
  isLocalHomeomorph := isLocalHomeomorph_comp_fst n X.z X.isLocalHomeomorph p
  e q := X.e q.1
  smooth_e := (smooth_prodFin_iff n X.z X.isLocalHomeomorph p _).2 fun _ => X.smooth_e
  levi_e := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z X.isLocalHomeomorph p]
    exact X.levi_e x ξ
  isCompact_le a := by
    have h : {q : M × Fin p | X.e q.1 ≤ a} = {x | X.e x ≤ a} ×ˢ (Set.univ : Set (Fin p)) := by
      ext q; simp
    rw [h]
    exact (X.isCompact_le a).prod isCompact_univ

end

end ReciprocityTheory.L2DbarEstimates
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop, ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos, ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR, ReciprocityTheory.L2DbarEstimates.SkodaWeights.IntegrableSliceProdFin, ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps, ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

theorem ontoWithBound (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] :
    OntoWithBoundStatement E H₁ H₂ := by
  intro G Gs θ Q c hc hadj hbd f hf
  let θ' : (Q × E) →ₗ[ℂ] H₁ := Gs ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E + θ ∘ₗ LinearMap.snd ℂ Q E
  let ℓ : (Q × E) →ₗ[ℂ] ℂ := (innerₛₗ ℂ f) ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E
  have hθ' : ∀ x : Q × E, θ' x = Gs x.1 + θ x.2 := fun x => rfl
  have hℓ : ∀ x : Q × E, ℓ x = ⟪f, (x.1 : H₂)⟫_ℂ := fun x => rfl
  have hA : 0 ≤ ‖f‖ ^ 2 / c := by positivity
  have hbound : ∀ x : Q × E, ‖ℓ x‖ ^ 2 ≤ ‖f‖ ^ 2 / c * ‖θ' x‖ ^ 2 := by
    intro x
    rw [hℓ, hθ']
    have h1 : ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ≤ ‖f‖ * ‖(x.1 : H₂)‖ := norm_inner_le_norm _ _
    have h2 := hbd x.1 x.1.2 x.2
    have h0 : 0 ≤ ‖⟪f, (x.1 : H₂)⟫_ℂ‖ := norm_nonneg _
    calc ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ^ 2 ≤ (‖f‖ * ‖(x.1 : H₂)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = ‖f‖ ^ 2 / c * (c * ‖(x.1 : H₂)‖ ^ 2) := by
        rw [mul_pow, div_mul_eq_mul_div, eq_div_iff hc.ne']
        ring
      _ ≤ ‖f‖ ^ 2 / c * ‖Gs x.1 + θ x.2‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hA
  obtain ⟨h, -, hnorm, hinner⟩ := rieszOnRange (Q × E) H₁ θ' ℓ _ hA hbound
  refine ⟨h, ?_, ?_, ?_⟩
  · intro u hu
    have hh : ⟪h, Gs u⟫_ℂ = ⟪f, u⟫_ℂ := by simpa [hθ', hℓ] using hinner (⟨u, hu⟩, 0)
    rw [← hadj u hu h, ← inner_conj_symm, hh, inner_conj_symm]
  · intro e
    simpa [hθ', hℓ] using hinner (0, e)
  · rw [le_div_iff₀ hc] at hnorm
    linarith [hnorm]

end ReciprocityTheory.L2DbarEstimates
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace

lemma hlin_vsq_pos {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))

theorem perpTrace : PerpTraceStatement := by
  intro p g hg
  have hs := hlin_vsq_pos hg
  refine ⟨fun i => sub_nonneg.mpr ((div_le_one hs).mpr
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))), ?_⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - vsq g / vsq g = _
  rw [div_self hs.ne']
  simp

end ReciprocityTheory.L2DbarEstimates.H
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.InnerProductSpace.Calculus\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IsLocalHomeomorphCompFst\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SmoothRLog\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral\nimport ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffAtComplex\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

noncomputable section

private theorem contDiffOn_vsq_gv_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => vsq (gv g (e.symm y))) e.target := by
  unfold vsq gv
  refine ContDiffOn.sum fun l _ => ?_
  have hd : DifferentiableOn ℂ (g l ∘ e.symm) e.target := hg l e he
  have ho : IsOpen e.target := e.open_target
  have h0 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    C.holo_contDiffOn_complex ho hd
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    h0.restrict_scalars ℝ
  exact (contDiff_norm_sq ℝ).comp_contDiffOn h1

theorem near_continuous_vsq {M : Type*} [TopologicalSpace M] {p : ℕ} (g : Fin p → M → ℂ)
    (hg : ∀ l, Continuous (g l)) : Continuous (fun x => vsq (gv g x)) := by
  unfold vsq gv
  exact continuous_finsetSum _ fun i _ => ((hg i).norm).pow 2

theorem near_continuous_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hx, he⟩ := hz x
    have hch : IsChart n z e := fun y _ => by rw [he]
    have h1 := (hf e hch).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
    have h2 : ContinuousAt (((fun y => (f y : ℂ)) ∘ e.symm) ∘ e) x :=
      ContinuousAt.comp (f := e) h1 (e.continuousAt hx)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

theorem near_smooth_slice {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (hN : ∀ x, gv g x ≠ 0) (u : M → ℂ) (hu : Holo n z u) (i : Fin p) :
    Smooth n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) := by
  intro e he
  have hu' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hu e he)).restrict_scalars ℝ
  have hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hg i e he)).restrict_scalars ℝ
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (g i (e.symm y))) e.target :=
    Complex.conjCLE.contDiff.comp_contDiffOn hg'
  have hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (((vsq (gv g (e.symm y)))⁻¹ : ℝ) : ℂ))
      e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_vsq_gv_comp_chart_symm n z g hg e he).inv
      fun y _ => (_root_.ReciprocityTheory.L2DbarEstimates.H.vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne')
  have hnum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y))) e.target := hu'.mul hc
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y)) /
    ((vsq (gv g (e.symm y)) : ℝ) : ℂ)) e.target
  exact (hnum.mul hv).congr fun y _ => by simp [div_eq_mul_inv]

theorem skodaNear (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaNearStatement n M := by
  intro X p g φ₀ t hH hp hg hN hφ₀ hLφ₀ ht u u' hu' huu' F0 hF0
  have hz := X.isLocalHomeomorph
  have hgc : ∀ l, Continuous (g l) := fun l =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg l))
  have huc : Continuous u' := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hu')
  have hNc := near_continuous_vsq g hgc
  have hNp : ∀ x, 0 < vsq (gv g x) := fun x => _root_.ReciprocityTheory.L2DbarEstimates.H.vsq_pos _ (hN x)
  have hW := skodaWeight n M X.z hz p g φ₀ t hg hN hφ₀ hLφ₀ ht.le
  have hWc : Continuous (skW g φ₀ t) := near_continuous_of_smoothR n X.z hz _ hW.1
  have hlogc : Continuous (fun x => Real.log (vsq (gv g x))) :=
    hNc.log fun x => (hNp x).ne'
  have hTr := fun x => perpTrace p (gv g x) (hN x)
  let F0f : M × Fin p → ℂ := fun q =>
    u' q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)
  let c : M × Fin p → ℝ := fun q =>
    ‖u' q.1‖ ^ 2 * (1 - ‖g q.2 q.1‖ ^ 2 / vsq (gv g q.1)) / (t * vsq (gv g q.1))
  have hc0 : ∀ q, 0 ≤ c q := fun q =>
    div_nonneg (mul_nonneg (by positivity) ((hTr q.1).1 q.2)) (mul_pos ht (hNp q.1)).le
  have hcm : Measurable c := measurable_from_prod_countable_left fun i => by
    have : Continuous (fun x =>
        ‖u' x‖ ^ 2 * (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) / (t * vsq (gv g x))) :=
      ((huc.norm.pow 2).mul (continuous_const.sub
        (((hgc i).norm.pow 2).div hNc fun x => (hNp x).ne'))).div
        (continuous_const.mul hNc) fun x => (mul_pos ht (hNp x)).ne'
    exact this.measurable
  have hsl : ∀ i, Smooth n X.z (fun x => F0f (x, i)) := fun i =>
    near_smooth_slice n X.z hz g hg hN u' hu' i
  have hF0fm : Measurable F0f := measurable_from_prod_countable_left fun i =>
    (Smooth.continuous n X.z hz _ (hsl i)).measurable
  have hF0fs : Smooth n (fun q : M × Fin p => X.z q.1) F0f :=
    (smooth_prodFin_iff n X.z hz p F0f).2 hsl
  have hph' : SmoothR n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) :=
    (smooth_prodFin_iff n X.z hz p _).2 fun _ => hW.1
  have hLph' : LeviNonneg n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) := by
    rintro ⟨x, i⟩ ξ
    rw [levi_prodFin n X.z hz p]
    exact hW.2.1 x ξ
  have hfm : Measurable (fun q => ENNReal.ofReal (c q)) := ENNReal.measurable_ofReal.comp hcm
  have hpt : ∀ (q : M × Fin p) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n (fun q : M × Fin p => X.z q.1) F0f q ξ‖ ^ 2) ≤
        ENNReal.ofReal (c q) *
          ENNReal.ofReal (Levi n (fun q : M × Fin p => X.z q.1) (fun q => skW g φ₀ t q.1) q ξ).re := by
    rintro ⟨x, i⟩ ξ
    have hd : dbarDot n (fun q : M × Fin p => X.z q.1) F0f (x, i) ξ =
        dbarDot n X.z (fun y => F0f (y, i)) x ξ := by
      simp only [dbarDot, db_prodFin n X.z hz p]
    rw [hd, levi_prodFin n X.z hz p, ← ENNReal.ofReal_mul (hc0 _)]
    exact ENNReal.ofReal_le_ofReal (skodaHyp n M X.z hz p g φ₀ t u' hg hu' hN hφ₀ hLφ₀ ht x i ξ)
  obtain ⟨F, hFh, hFb⟩ := hH (EtaleStein.prodFin n X p) (fun q => skW g φ₀ t q.1) F0f
    (fun q => ENNReal.ofReal (c q)) hph' hLph' hF0fs hfm hpt
  have hph'm : Measurable (fun q : M × Fin p => skW g φ₀ t q.1) :=
    hWc.measurable.comp measurable_fst
  have hψm : Measurable (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    (hWc.add hlogc).measurable
  have hpt0 : 0 ≤ ((p : ℝ) - 1) / t :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hp)) ht.le
  have hEm : Measurable (fun q : M × Fin p =>
      ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))) :=
    hfm.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'm.neg))
  have hR : ∫⁻ q, ENNReal.ofReal (c q) * ENNReal.ofReal (Real.exp (-skW g φ₀ t q.1))
      ∂vol n (fun q : M × Fin p => X.z q.1) =
      ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := by
    have hmi : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable (fun x : M =>
        ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))) :=
      fun i _ => hEm.comp measurable_prodMk_right
    rw [lintegral_vol_prodFin n X.z hz p _ hEm, ← lintegral_finsetSum _ hmi]
    unfold wint
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    have hs : ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) = (p : ℝ) - 1 := (hTr x).2
    calc ∑ i, ENNReal.ofReal (c (x, i)) * ENNReal.ofReal (Real.exp (-skW g φ₀ t (x, i).1))
        = ∑ i, ENNReal.ofReal (c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hc0 _)).symm
      _ = ENNReal.ofReal (∑ i, c (x, i) * Real.exp (-skW g φ₀ t x)) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg (hc0 _) (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (((p : ℝ) - 1) / t *
            (‖u' x‖ ^ 2 * Real.exp (-(skW g φ₀ t x + Real.log (vsq (gv g x)))))) := by
          congr 1
          have hsum : ∑ i, c (x, i) * Real.exp (-skW g φ₀ t x) =
              (‖u' x‖ ^ 2 / (t * vsq (gv g x)) * Real.exp (-skW g φ₀ t x)) *
                ∑ i, (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [c]
            ring
          have hNx := hNp x
          rw [hsum, hs, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hNx]
          field_simp
      _ = _ := ENNReal.ofReal_mul hpt0
  have hl2 := l2w n M X.z _ hψm
  have hl2' := l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1) _ hph'm
  obtain ⟨hu_fin, hu_norm⟩ := hl2.2.1 u
  have hwu : wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) =
      wint n X.z (u : M → ℂ) (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) :=
    lintegral_congr_ae (huu'.mono fun x hx => by dsimp only; rw [hx])
  have hR_fin : ENNReal.ofReal (((p : ℝ) - 1) / t) *
      wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hwu ▸ hu_fin)
  have hFb' : wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
      (fun q => skW g φ₀ t q.1) ≤ ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x))) := hR ▸ hFb
  have hwF0 : wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) < ⊤ := by
    have h1 := (hl2'.2.1 F0).1
    have h2 : wint n (fun q : M × Fin p => X.z q.1) (F0 : M × Fin p → ℂ)
        (fun q => skW g φ₀ t q.1) = wint n (fun q : M × Fin p => X.z q.1) F0f
        (fun q => skW g φ₀ t q.1) := lintegral_congr_ae (hF0.mono fun q hq => by dsimp only at hq ⊢; rw [hq])
    exact h2 ▸ h1
  have hFc : Continuous F :=
    Smooth.continuous n _ (EtaleStein.prodFin n X p).isLocalHomeomorph _ (Holo.smooth n _ _ hFh)
  have hwF : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) < ⊤ := by
    have hle : wint n (fun q : M × Fin p => X.z q.1) F (fun q => skW g φ₀ t q.1) ≤
        2 * wint n (fun q : M × Fin p => X.z q.1) F0f (fun q => skW g φ₀ t q.1) +
          2 * wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q)
            (fun q => skW g φ₀ t q.1) := by
      unfold wint
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_add_left]
      · refine lintegral_mono fun q => ?_
        have hE := Real.exp_pos (-skW g φ₀ t q.1)
        have h3 : ‖F q‖ ≤ ‖F0f q‖ + ‖F0f q - F q‖ := by
          simpa using norm_sub_le (F0f q) (F0f q - F q)
        have h4 : ‖F q‖ ^ 2 ≤ 2 * ‖F0f q‖ ^ 2 + 2 * ‖F0f q - F q‖ ^ 2 := by
          nlinarith [sq_nonneg (‖F0f q‖ - ‖F0f q - F q‖), norm_nonneg (F q),
            norm_nonneg (F0f q), norm_nonneg (F0f q - F q)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_le_mul_of_nonneg_right h4 hE.le]
      · exact measurable_const.mul (ENNReal.measurable_ofReal.comp
          (((hF0fm.norm.pow_const 2).mul (Real.measurable_exp.comp hph'm.neg))))
    exact hle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwF0,
      ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hFb'.trans_lt hR_fin)⟩)
  obtain ⟨Fc, hFcF⟩ := hl2'.2.2 F hFc.aestronglyMeasurable hwF
  refine ⟨Fc, ⟨F, hFh, (hl2'.1 (fun q => (Fc : M × Fin p → ℂ) q = F q)).2 hFcF⟩, ?_⟩
  rw [(hl2'.2.1 (F0 - Fc)).2]
  have hsub : wint n (fun q : M × Fin p => X.z q.1) ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ)
      (fun q => skW g φ₀ t q.1) =
      wint n (fun q : M × Fin p => X.z q.1) (fun q => F0f q - F q) (fun q => skW g φ₀ t q.1) := by
    refine lintegral_congr_ae ?_
    have h1 := (hl2'.1 (fun q => ((F0 - Fc : WeightedL2 n _ _) : M × Fin p → ℂ) q =
      ((F0 : M × Fin p → ℂ) - (Fc : M × Fin p → ℂ)) q)).1 (Lp.coeFn_sub F0 Fc)
    filter_upwards [h1, hF0, hFcF] with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [hsub]
  calc _ ≤ (ENNReal.ofReal (((p : ℝ) - 1) / t) *
        wint n X.z u' (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))).toReal :=
        ENNReal.toReal_mono hR_fin.ne hFb'
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpt0, hwu, hu_norm]

end

end ReciprocityTheory.L2DbarEstimates.H
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.IntegrableSliceProdFin =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.SkodaWeights.IntegrableSliceProdFin", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace

noncomputable section

theorem norm_sum_mul_sq_le {p : ℕ} (g a : Fin p → ℂ) :
    ‖∑ i, g i * a i‖ ^ 2 ≤ vsq g * ∑ i, ‖a i‖ ^ 2 := by
  unfold vsq
  have h1 : ‖∑ i, g i * a i‖ ≤ ∑ i, ‖g i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖g i‖) (fun i => ‖a i‖)
  calc ‖∑ i, g i * a i‖ ^ 2 ≤ (∑ i, ‖g i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem pt_G {p : ℕ} (g a : Fin p → ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ‖∑ i, g i * a i‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) ≤
      ∑ i, ‖a i‖ ^ 2 * Real.exp (-c) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  rw [hexp, ← Finset.sum_mul]
  have hcs := norm_sum_mul_sq_le g a
  have h1 : ‖∑ i, g i * a i‖ ^ 2 / vsq g ≤ ∑ i, ‖a i‖ ^ 2 := by
    rw [div_le_iff₀ hN, mul_comm]
    exact hcs
  have he := Real.exp_pos (-c)
  calc ‖∑ i, g i * a i‖ ^ 2 * (Real.exp (-c) / vsq g)
      = (‖∑ i, g i * a i‖ ^ 2 / vsq g) * Real.exp (-c) := by ring
    _ ≤ (∑ i, ‖a i‖ ^ 2) * Real.exp (-c) := by gcongr

theorem pt_Gs {p : ℕ} (g : Fin p → ℂ) (w : ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ∑ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 * Real.exp (-c) =
      ‖w‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  have hterm : ∀ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 =
      ‖w‖ ^ 2 * ‖g i‖ ^ 2 / vsq g ^ 2 := by
    intro i
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    ring
  have hv : (∑ i, ‖g i‖ ^ 2) = vsq g := rfl
  have hN' : vsq g ≠ 0 := hN.ne'
  rw [hexp]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, hv]
  field_simp

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

private theorem vol_prod_fin_apply_eq_sum_preimage (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (A : Set (M × Fin p)) (hA : MeasurableSet A) :
    vol n (fun q : M × Fin p => z q.1) A = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' A) := by
  rw [vol_prodFin_eq n z hz p, FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => Measure.map_apply measurable_prodMk_right hA

private theorem map_prodMk_right_vol_le_vol_prod_fin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (i : Fin p) :
    (vol n z).map (fun x => (x, i)) ≤ vol n (fun q : M × Fin p => z q.1) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply measurable_prodMk_right hs, vol_prod_fin_apply_eq_sum_preimage z hz p s hs]
  exact Finset.single_le_sum (f := fun j => vol n z ((fun x => (x, j)) ⁻¹' s))
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem ae_slice_prodFin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    {P : M × Fin p → Prop} (hP : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q) (i : Fin p) :
    ∀ᵐ x ∂vol n z, P (x, i) := by
  exact ae_of_ae_map measurable_prodMk_right.aemeasurable (ae_mono (map_prodMk_right_vol_le_vol_prod_fin z hz p i) hP)

theorem ae_lift_prodFin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (hP : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by
  rw [ae_iff] at hP ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hP
  refine measure_mono_null (t := N ×ˢ Set.univ) (fun q hq => ⟨hsub hq, Set.mem_univ _⟩) ?_
  rw [vol_prod_fin_apply_eq_sum_preimage z hz p _ (hNm.prod MeasurableSet.univ)]
  simp [Set.mk_preimage_prod_left, hN0]

theorem measurable_vsq {p : ℕ} {g : Fin p → M → ℂ} (hg : ∀ l, Measurable (g l)) :
    Measurable (fun x => vsq (gv g x)) := by
  simp only [vsq, gv]
  exact Finset.measurable_sum _ fun i _ => ((hg i).norm).pow_const 2

theorem wint_G_le (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (h : M × Fin p → ℂ) (hh : Measurable h) :
    wint n z (fun x => ∑ i, g i x * h (x, i)) (fun x => φ x + Real.log (vsq (gv g x))) ≤
      wint n (fun q : M × Fin p => z q.1) h (fun q => φ q.1) := by
  show ∫⁻ x, ENNReal.ofReal (‖∑ i, g i x * h (x, i)‖ ^ 2 *
      Real.exp (-(φ x + Real.log (vsq (gv g x))))) ∂vol n z ≤
    ∫⁻ q, ENNReal.ofReal (‖h q‖ ^ 2 * Real.exp (-φ q.1)) ∂vol n (fun q : M × Fin p => z q.1)
  have hFm : Measurable (fun q : M × Fin p => ENNReal.ofReal (‖h q‖ ^ 2 * Real.exp (-φ q.1))) :=
    ((hh.norm.pow_const 2).mul (hφ.comp measurable_fst).neg.exp).ennreal_ofReal
  rw [lintegral_vol_prodFin n z hz p _ hFm,
    ← MeasureTheory.lintegral_finsetSum (f := fun i a => ENNReal.ofReal (‖h (a, i)‖ ^ 2 *
      Real.exp (-φ (a, i).1))) _ fun i _ => hFm.comp measurable_prodMk_right]
  refine lintegral_mono fun x => ?_
  beta_reduce
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  exact ENNReal.ofReal_le_ofReal (pt_G (gv g x) (fun i => h (x, i)) (φ x) (hN x))

theorem wint_Gs_eq (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (hg : ∀ l, Measurable (g l)) (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (w : M → ℂ) (hw : Measurable w) :
    wint n (fun q : M × Fin p => z q.1)
        (fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
        (fun q => φ q.1) =
      wint n z w (fun x => φ x + Real.log (vsq (gv g x))) := by
  show ∫⁻ q, ENNReal.ofReal (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
      Real.exp (-φ q.1)) ∂vol n (fun q : M × Fin p => z q.1) =
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * Real.exp (-(φ x + Real.log (vsq (gv g x))))) ∂vol n z
  have hvs := measurable_vsq hg
  have hg2 : Measurable (fun q : M × Fin p => g q.2 q.1) := by
    have e : (fun q : M × Fin p => g q.2 q.1) = fun q => ∑ j, if q.2 = j then g j q.1 else 0 := by
      funext q
      simp
    rw [e]
    exact Finset.measurable_sum _ fun j _ => Measurable.ite
      ((measurableSet_singleton j).preimage measurable_snd) ((hg j).comp measurable_fst)
      measurable_const
  have hFm : Measurable (fun q : M × Fin p => ENNReal.ofReal
      (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ q.1))) := by
    refine (((((hw.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp hg2)).div
      (Complex.continuous_ofReal.measurable.comp (hvs.comp measurable_fst))).norm.pow_const 2).mul
      (hφ.comp measurable_fst).neg.exp).ennreal_ofReal
  rw [lintegral_vol_prodFin n z hz p _ hFm,
    ← MeasureTheory.lintegral_finsetSum (f := fun i a => ENNReal.ofReal
      (‖w (a, i).1 * (starRingEnd ℂ) (g (a, i).2 (a, i).1) / ((vsq (gv g (a, i).1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ (a, i).1))) _ fun i _ => hFm.comp measurable_prodMk_right]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  congr 1
  exact pt_Gs (gv g x) (w x) (φ x) (hN x)

end

end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.IntegrableSliceProdFin =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.CStarAlgebra.Module.Constructions\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.InnerProductSpace.Adjoint\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.IntegrableSliceProdFin\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open scoped ENNReal InnerProductSpace

private theorem wint_congr_ae (n : ℕ) {N : Type*} [MeasurableSpace N] (z : N → V n)
    (ψ : N → ℝ) {f₁ f₂ : N → ℂ} (h : f₁ =ᵐ[vol n z] f₂) : wint n z f₁ ψ = wint n z f₂ ψ := by
  unfold wint
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

private theorem exists_pow_mul_eq_eval₂_theta (n : ℕ) {N : Type*} [MeasurableSpace N] (z : N → V n) (ψ : N → ℝ)
    (hψ : Measurable ψ) (F : WeightedL2 n z ψ) :
    ∃ f : N → ℂ, Measurable f ∧ (F : N → ℂ) =ᵐ[vol n z] f := by
  obtain ⟨A1, -, -⟩ := l2w n N z ψ hψ
  refine ⟨(Lp.aestronglyMeasurable F).mk _,
    (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable, ?_⟩
  exact (A1 (fun x => (F : N → ℂ) x = (Lp.aestronglyMeasurable F).mk _ x)).mp
    (Lp.aestronglyMeasurable F).ae_eq_mk

private theorem exists_clm_weightedL2_of_bounded (n : ℕ) {N₁ N₂ : Type*} [MeasurableSpace N₁] [MeasurableSpace N₂]
    (z₁ : N₁ → V n) (z₂ : N₂ → V n) (ψ₁ : N₁ → ℝ) (ψ₂ : N₂ → ℝ)
    (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂) (T : (N₁ → ℂ) → (N₂ → ℂ))
    (hT : ∀ (a : ℂ) (f₁ f₂ : N₁ → ℂ), T (fun x => a * f₁ x + f₂ x) = fun y => a * T f₁ y + T f₂ y)
    (hTae : ∀ f₁ f₂ : N₁ → ℂ, f₁ =ᵐ[vol n z₁] f₂ → T f₁ =ᵐ[vol n z₂] T f₂)
    (hex : ∀ F : WeightedL2 n z₁ ψ₁, ∃ H : WeightedL2 n z₂ ψ₂, (H : N₂ → ℂ) =ᵐ[vol n z₂] T F)
    (hb : ∀ (F : WeightedL2 n z₁ ψ₁) (H : WeightedL2 n z₂ ψ₂), (H : N₂ → ℂ) =ᵐ[vol n z₂] T F → ‖H‖ ≤ ‖F‖) :
    ∃ L : WeightedL2 n z₁ ψ₁ →L[ℂ] WeightedL2 n z₂ ψ₂, ∀ F, (L F : N₂ → ℂ) =ᵐ[vol n z₂] T F := by
  obtain ⟨A1, -, -⟩ := l2w n N₁ z₁ ψ₁ hψ₁
  obtain ⟨B1, -, -⟩ := l2w n N₂ z₂ ψ₂ hψ₂
  choose L hL using hex
  have key : ∀ (a : ℂ) (F₁ F₂ : WeightedL2 n z₁ ψ₁), L (a • F₁ + F₂) = a • L F₁ + L F₂ := by
    intro a F₁ F₂
    apply Lp.ext
    have h2 : ((a • F₁ + F₂ : WeightedL2 n z₁ ψ₁) : N₁ → ℂ) =ᵐ[vol n z₁] fun x => a * F₁ x + F₂ x :=
      (A1 (fun x => ((a • F₁ + F₂ : WeightedL2 n z₁ ψ₁) : N₁ → ℂ) x = a * F₁ x + F₂ x)).mp (by
        filter_upwards [Lp.coeFn_add (a • F₁) F₂, Lp.coeFn_smul a F₁] with x hx1 hx2
        rw [hx1, Pi.add_apply, hx2, Pi.smul_apply, smul_eq_mul])
    have h3 : ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) =ᵐ[vol n z₂]
        fun y => a * L F₁ y + L F₂ y :=
      (B1 (fun y => ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y = a * L F₁ y + L F₂ y)).mp (by
        filter_upwards [Lp.coeFn_add (a • L F₁) (L F₂), Lp.coeFn_smul a (L F₁)] with y hy1 hy2
        rw [hy1, Pi.add_apply, hy2, Pi.smul_apply, smul_eq_mul])
    refine (B1 (fun y => ((L (a • F₁ + F₂) : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y =
      ((a • L F₁ + L F₂ : WeightedL2 n z₂ ψ₂) : N₂ → ℂ) y)).mpr ?_
    filter_upwards [hL (a • F₁ + F₂), hTae _ _ h2, h3, hL F₁, hL F₂] with y e1 e2 e3 e4 e5
    rw [e1, e2, hT a (F₁ : N₁ → ℂ) (F₂ : N₁ → ℂ), e3, e4, e5]
  have L0 : L 0 = 0 := by
    have h := key 1 0 0
    simp only [one_smul, add_zero] at h
    have h' : L 0 + 0 = L 0 + L 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  refine ⟨LinearMap.mkContinuous
    { toFun := L
      map_add' := fun F₁ F₂ => by simpa using key 1 F₁ F₂
      map_smul' := fun c F => by simpa [L0] using key c F 0 } 1
    (fun F => by simpa using hb F (L F) (hL F)), fun F => hL F⟩

private theorem inner_isometry_eq_inner_left_inverse {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (S : F →L[ℂ] E) (G : E →L[ℂ] F) (hS : ∀ w, ‖S w‖ = ‖w‖) (hG : ∀ h, ‖G h‖ ≤ ‖h‖)
    (hGS : ∀ w, G (S w) = w) (w : F) (h : E) : ⟪S w, h⟫_ℂ = ⟪w, G h⟫_ℂ := by
  set A := ContinuousLinearMap.adjoint S with hA
  let Si : F →ₗᵢ[ℂ] E := { toLinearMap := S.toLinearMap, norm_map' := hS }
  have hSS : ∀ x y, ⟪S x, S y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => Si.inner_map_map x y
  have hAS : ∀ x, A (S x) = x := by
    intro x
    apply ext_inner_left ℂ
    intro v
    rw [hA, ContinuousLinearMap.adjoint_inner_right, hSS]
  set k := h - S (A h) with hk0
  have hk : ∀ y, ⟪S y, k⟫_ℂ = 0 := by
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← hA, hk0, map_sub, hAS, sub_self,
      inner_zero_right]
  have hGk : G k = 0 := by
    by_contra hne
    have ha : 0 < ‖G k‖ := norm_pos_iff.mpr hne
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖k‖ ^ 2 / ‖G k‖ ^ 2 := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hsa : s * ‖G k‖ ^ 2 = ‖k‖ ^ 2 := by
      rw [hs]; exact div_mul_cancel₀ _ (pow_pos ha 2).ne'
    have h1 : ‖G (S ((s : ℂ) • G k) + k)‖ ≤ ‖S ((s : ℂ) • G k) + k‖ := hG _
    rw [map_add (f := _), hGS] at h1
    have h2 : ‖(s : ℂ) • G k + G k‖ = (s + 1) * ‖G k‖ := by
      have e : (s : ℂ) • G k + G k = ((s + 1 : ℝ) : ℂ) • G k := by
        rw [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h3 : ‖S ((s : ℂ) • G k) + k‖ * ‖S ((s : ℂ) • G k) + k‖ =
        (s * ‖G k‖) * (s * ‖G k‖) + ‖k‖ * ‖k‖ := by
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hk _), hS, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    rw [h2] at h1
    have h4 := mul_self_le_mul_self (by positivity) h1
    nlinarith [h3, h4, hsa, mul_pos ha ha, mul_nonneg hs0 (mul_self_nonneg ‖G k‖)]
  have hdec : h = S (A h) + k := by rw [hk0]; abel
  have hGh : G h = A h := by
    calc G h = G (S (A h) + k) := by rw [← hdec]
      _ = A h := by rw [map_add (f := _), hGS, hGk, add_zero]
  rw [hGh, hA, ContinuousLinearMap.adjoint_inner_right]

theorem skodaOps (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaOpsStatement n M := by
  intro X p g φ hg hgv hφ
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hgc : ∀ l, Continuous (g l) := fun l =>
    Smooth.continuous n X.z hz (g l) (Holo.smooth n X.z (g l) (hg l))
  have hgm : ∀ l, Measurable (g l) := fun l => (hgc l).measurable
  have hgq : Measurable fun q : M × Fin p => g q.2 q.1 :=
    measurable_from_prod_countable_left fun i => hgm i
  have hN : ∀ x, 0 < vsq (gv g x) := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, gv g x i ≠ 0 := by
      by_contra! hc
      exact hgv x (funext hc)
    have h1 : 0 < ‖gv g x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    have h2 : ‖gv g x i‖ ^ 2 ≤ ∑ j, ‖gv g x j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖gv g x j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    unfold vsq
    linarith
  have hvc : Continuous fun x => vsq (gv g x) := by
    show Continuous fun x => ∑ i, ‖g i x‖ ^ 2
    exact continuous_finsetSum _ fun i _ => ((hgc i).norm).pow 2
  have hvm : Measurable fun x => vsq (gv g x) := hvc.measurable
  have hφm : Measurable φ := hφ.measurable
  have hψm : Measurable fun x => φ x + Real.log (vsq (gv g x)) :=
    hφm.add (Real.measurable_log.comp hvm)
  have hψpm : Measurable fun x : M × Fin p => φ x.1 := hφm.comp measurable_fst
  obtain ⟨A1, A2, A3⟩ := l2w n M X.z (fun x => φ x + Real.log (vsq (gv g x))) hψm
  obtain ⟨B1, B2, B3⟩ := l2w n (M × Fin p) (fun q : M × Fin p => X.z q.1)
    (fun x : M × Fin p => φ x.1) hψpm
  have hcn : Measurable fun q : M × Fin p => ((vsq (gv g q.1) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hvm.comp measurable_fst)
  have hcj : Measurable fun q : M × Fin p => (starRingEnd ℂ) (g q.2 q.1) :=
    Complex.continuous_conj.measurable.comp hgq
  have hlift : ∀ f₁ f₂ : M → ℂ, f₁ =ᵐ[vol n X.z] f₂ →
      ∀ᵐ q ∂vol n (fun q : M × Fin p => X.z q.1), f₁ q.1 = f₂ q.1 := fun f₁ f₂ h =>
    ae_lift_prodFin X.z hz p (P := fun x => f₁ x = f₂ x) h
  have hslice : ∀ h₁ h₂ : M × Fin p → ℂ, h₁ =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] h₂ →
      ∀ᵐ x ∂vol n X.z, ∀ i, h₁ (x, i) = h₂ (x, i) := fun h₁ h₂ h =>
    ae_all_iff.mpr fun i => ae_slice_prodFin X.z hz p (P := fun q => h₁ q = h₂ q) h i
  have hcancel : ∀ (x : M) (c : ℂ),
      ∑ i, g i x * (c * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ)) = c := by
    intro x c
    have hV : ((vsq (gv g x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN x).ne'
    have hs : ∑ i, g i x * (starRingEnd ℂ) (g i x) = ((vsq (gv g x) : ℝ) : ℂ) := by
      rw [show vsq (gv g x) = ∑ i, ‖g i x‖ ^ 2 from rfl, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc ∑ i, g i x * (c * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ))
        = c * (∑ i, g i x * (starRingEnd ℂ) (g i x)) / ((vsq (gv g x) : ℝ) : ℂ) := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = c := by rw [hs, mul_div_assoc, div_self hV, mul_one]
  have hGsn : ∀ (w : WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x))))
      (H : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x : M × Fin p => φ x.1)),
      (H : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        (fun q => (w : M → ℂ) q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) →
      ‖H‖ = ‖w‖ := by
    intro w H hH
    obtain ⟨wm, hwm, hwae⟩ := exists_pow_mul_eq_eval₂_theta n X.z _ hψm w
    have hH' : (H : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        (fun q => wm q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) := by
      filter_upwards [hH, hlift _ _ hwae] with q h1 h2
      rw [h1, h2]
    have e : ‖H‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [(B2 H).2, (A2 w).2, wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hH',
        wint_Gs_eq X.z hz p g hgm φ hφm hN wm hwm,
        wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hwae]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp e
  have hGb : ∀ (h : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x : M × Fin p => φ x.1))
      (H : WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x)))),
      (H : M → ℂ) =ᵐ[vol n X.z] (fun x => ∑ i, g i x * (h : M × Fin p → ℂ) (x, i)) →
      ‖H‖ ≤ ‖h‖ := by
    intro h H hH
    obtain ⟨hm, hhm, hhae⟩ := exists_pow_mul_eq_eval₂_theta n (fun q : M × Fin p => X.z q.1) _ hψpm h
    have hH' : (H : M → ℂ) =ᵐ[vol n X.z] (fun x => ∑ i, g i x * hm (x, i)) := by
      filter_upwards [hH, hslice _ _ hhae] with x h1 h2
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
    have hfin : wint n (fun q : M × Fin p => X.z q.1) hm (fun x : M × Fin p => φ x.1) ≠ ⊤ := by
      rw [← wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
      exact (B2 h).1.ne
    have e : ‖H‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [(A2 H).2, (B2 h).2,
        wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hH',
        wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
      exact ENNReal.toReal_mono hfin (wint_G_le X.z hz p g φ hφm hN hm hhm)
    nlinarith [norm_nonneg H, norm_nonneg h]
  obtain ⟨Gs, hGs⟩ := exists_clm_weightedL2_of_bounded n X.z (fun q : M × Fin p => X.z q.1)
    (fun x => φ x + Real.log (vsq (gv g x))) (fun x : M × Fin p => φ x.1) hψm hψpm
    (fun f q => f q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
    (fun a f₁ f₂ => by funext q; beta_reduce; ring)
    (fun f₁ f₂ h => by
      filter_upwards [hlift f₁ f₂ h] with q hq
      rw [hq])
    (fun w => by
      obtain ⟨wm, hwm, hwae⟩ := exists_pow_mul_eq_eval₂_theta n X.z _ hψm w
      have hmeas : Measurable (fun q : M × Fin p =>
          wm q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)) :=
        ((hwm.comp measurable_fst).mul hcj).div hcn
      obtain ⟨H, hH⟩ := B3 _ hmeas.aestronglyMeasurable (by
        rw [wint_Gs_eq X.z hz p g hgm φ hφm hN wm hwm,
          ← wint_congr_ae n X.z (fun x => φ x + Real.log (vsq (gv g x))) hwae]
        exact (A2 w).1)
      refine ⟨H, ?_⟩
      filter_upwards [hH, hlift _ _ hwae] with q h1 h2
      rw [h1, h2])
    (fun w H hH => le_of_eq (hGsn w H hH))
  obtain ⟨G, hG⟩ := exists_clm_weightedL2_of_bounded n (fun q : M × Fin p => X.z q.1) X.z (fun x : M × Fin p => φ x.1)
    (fun x => φ x + Real.log (vsq (gv g x))) hψpm hψm
    (fun h x => ∑ i, g i x * h (x, i))
    (fun a h₁ h₂ => by
      funext x
      beta_reduce
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun h₁ h₂ hh => by
      filter_upwards [hslice h₁ h₂ hh] with x hx
      exact Finset.sum_congr rfl fun i _ => by rw [hx i])
    (fun h => by
      obtain ⟨hm, hhm, hhae⟩ := exists_pow_mul_eq_eval₂_theta n (fun q : M × Fin p => X.z q.1) _ hψpm h
      have hmeas : Measurable (fun x : M => ∑ i, g i x * hm (x, i)) :=
        Finset.measurable_sum _ fun i _ => (hgm i).mul (hhm.comp (by fun_prop))
      obtain ⟨H, hH⟩ := A3 _ hmeas.aestronglyMeasurable
        (lt_of_le_of_lt (wint_G_le X.z hz p g φ hφm hN hm hhm) (by
          rw [← wint_congr_ae n _ (fun x : M × Fin p => φ x.1) hhae]
          exact (B2 h).1))
      refine ⟨H, ?_⟩
      filter_upwards [hH, hslice _ _ hhae] with x h1 h2
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i])
    (fun h H hH => hGb h H hH)
  have hGsiso : ∀ w, ‖Gs w‖ = ‖w‖ := fun w => hGsn w (Gs w) (hGs w)
  have hGS : ∀ w, G (Gs w) = w := by
    intro w
    apply Lp.ext
    refine (A1 (fun x => (G (Gs w) : M → ℂ) x = (w : M → ℂ) x)).mpr ?_
    filter_upwards [hG (Gs w), hslice _ _ (hGs w)] with x h1 h2
    rw [h1]
    calc ∑ i, g i x * (Gs w : M × Fin p → ℂ) (x, i)
        = ∑ i, g i x * ((w : M → ℂ) x * (starRingEnd ℂ) (g i x) / ((vsq (gv g x) : ℝ) : ℂ)) :=
          Finset.sum_congr rfl fun i _ => by rw [h2 i]
      _ = (w : M → ℂ) x := hcancel x _
  exact ⟨G, Gs, hG, hGs, fun w h => inner_isometry_eq_inner_left_inverse Gs G hGsiso (fun h => hGb h (G h) (hG h)) hGS w h,
    hGsiso⟩

end ReciprocityTheory.L2DbarEstimates.H
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed\npublic import Mathlib.Topology.Connected.Separation\npublic import Mathlib.Topology.Separation.CompletelyRegular\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq\npublic import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IsLocalHomeomorphCompFst\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph\nimport ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset\npublic import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR\npublic import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps\nimport ReciprocityTheory.L2DbarEstimates.SkodaWeights.SmoothRLog\nimport ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

section SlopeTestRemainingChoices

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem vol_prodFin_apply (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (S : Set (M × Fin p)) (hS : MeasurableSet S) :
    vol n (fun q : M × Fin p => z q.1) S = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' S) :=
  SkodaOperators.vol_prod_fin_apply_eq_sum_preimage z hz p S hS

theorem ae_fst_prodFin (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (h : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 :=
  SkodaOperators.ae_lift_prodFin z hz p h

theorem ae_slice_prodFin (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    {P : M × Fin p → Prop} (h : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q) (i : Fin p) :
    ∀ᵐ x ∂vol n z, P (x, i) :=
  SkodaOperators.ae_slice_prodFin z hz p h i

theorem holo_finsum (n : ℕ) (z : M → V n) {p : ℕ} (F : Fin p → M → ℂ) (hF : ∀ i, Holo n z (F i)) :
    Holo n z (fun x => ∑ i, F i x) := by
  have h : Holo n z (∑ i, F i) :=
    Finset.sum_induction F (fun f : M → ℂ => Holo n z f)
      (fun a b ha hb => Holo.add n z a b ha hb) (Holo.const n z 0) (fun i _ => hF i)
  have e : (fun x => ∑ i, F i x) = ∑ i, F i := by
    ext x
    simp [Finset.sum_apply]
  rw [e]
  exact h

end SlopeTestRemainingChoices

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hH : ∀ p : ℕ, HStatement n (M × Fin p))
    (hB : ∀ p : ℕ, NeedBergmanClosed n (M × Fin p)) :
    SStatement n M := by
  intro X p g ph0 t f hp hg hnz hs hl ht hf hA
  have hz := X.isLocalHomeomorph
  have hz' : IsLocalHomeomorph (fun q : M × Fin p => X.z q.1) :=
    isLocalHomeomorph_comp_fst n X.z hz p
  have hp1 : 1 ≤ p := by omega
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have ht0 : 0 < t := by linarith
  have hgv : ∀ x, gv g x ≠ 0 := fun x h => by
    obtain ⟨i, hi⟩ := hnz x; exact hi (congrFun h i)
  have hN : ∀ x, 0 < vsq (gv g x) := fun x => by
    obtain ⟨i, hi⟩ := hnz x
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg i))
  have hfc : Continuous f := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hf)
  have hNc : Continuous fun x => vsq (gv g x) :=
    continuous_finsetSum _ fun i _ => ((hgc i).norm.pow 2)
  have hW := skodaWeight n M X.z hz p g ph0 t hg hgv hs hl ht0.le
  have hφc : Continuous (skW g ph0 t) :=
    (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hW.1)).congr fun x => Complex.ofReal_re _
  have hψ₂c : Continuous fun x => skW g ph0 t x + Real.log (vsq (gv g x)) :=
    hφc.add (hNc.log fun x => (hN x).ne')
  have hψ₁c : Continuous fun x : M × Fin p => skW g ph0 t x.1 := hφc.comp continuous_fst
  have hl2 := l2w n M X.z _ hψ₂c.measurable
  have hl1 := l2w n (M × Fin p) (fun q => X.z q.1) _ hψ₁c.measurable
  obtain ⟨G, Gs, hG, hGs, hadj, hiso⟩ := skodaOps n M X p g (skW g ph0 t) hg hgv hφc
  have hKc := hB p (fun q => X.z q.1) hz' _ hψ₁c
  have : CompleteSpace (holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1)) :=
    hKc.completeSpace_coe
  set K := holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1) with hKdef
  set Q := holSub n X.z (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) with hQdef
  set c : ℝ := (t - ((p : ℝ) - 1)) / t with hcdef
  have hc : 0 < c := div_pos (by linarith) ht0
  have hc' : ∀ r : ℝ, c * r = r - ((p : ℝ) - 1) / t * r := fun r => by
    rw [hcdef]; field_simp

  have hnear : ∀ u ∈ Q, c * ‖u‖ ^ 2 ≤ ‖K.orthogonalProjectionOnto (Gs u)‖ ^ 2 := by
    intro u hu
    obtain ⟨u', hu', huu'⟩ := hu
    have huv : (u : M → ℂ) =ᵐ[vol n X.z] u' := (hl2.1 _).1 huu'
    have hF0 : (Gs u : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        fun x => u' x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ) := by
      filter_upwards [hGs u, ae_fst_prodFin n X.z hz p huv] with q h1 h2
      rw [h1, h2]
    obtain ⟨F, hFK, hFd⟩ :=
      skodaNear n M X p g ph0 t (hH p) hp1 hg hgv hs hl ht0 u u' hu' huv (Gs u) hF0
    have hya : Gs u - K.starProjection (Gs u) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (Gs u)
    have hperp : ⟪K.starProjection (Gs u), Gs u - K.starProjection (Gs u)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto (Gs u)).2 hya
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp
    rw [add_sub_cancel, hiso u] at hpy
    have hmin : ‖Gs u - K.starProjection (Gs u)‖ ≤ ‖Gs u - F‖ := by
      rw [Submodule.starProjection_minimal (U := K) (Gs u)]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨F, hFK⟩ : K)
    have hmin2 := pow_le_pow_left₀ (norm_nonneg _) hmin 2
    have hnorm : ‖K.orthogonalProjectionOnto (Gs u)‖ = ‖K.starProjection (Gs u)‖ := rfl
    rw [hnorm, hc']
    nlinarith [hpy, hmin2, hFd]

  have hAeq : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph0 x)) ∂vol n X.z =
      wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
    unfold wint
    refine lintegral_congr fun x => ?_
    rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x), mul_assoc,
      ← Real.exp_add]
    congr 3
    simp only [skW]; ring
  obtain ⟨fL, hfL⟩ := hl2.2.2 f hfc.aestronglyMeasurable (hAeq ▸ hA)
  have hfLQ : fL ∈ Q := ⟨f, hf, (hl2.1 _).2 hfL⟩
  obtain ⟨⟨hv, hvK⟩, hhG, -, hhn⟩ := ontoWithBound ℂ K _ ((G : _ →ₗ[ℂ] _).comp K.subtype)
    ((K.orthogonalProjectionOnto.comp Gs : _ →L[ℂ] K) : _ →ₗ[ℂ] K) 0 Q c hc
    (fun u _ x => by simp [hadj]) (fun u hu e => by simpa using hnear u hu) fL hfLQ
  have hhn' : c * ‖hv‖ ^ 2 ≤ ‖fL‖ ^ 2 := hhn
  obtain ⟨hh', hhol', hae'⟩ := hvK
  have hae'v : (hv : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] hh' :=
    (hl1.1 _).1 hae'
  have hslice : ∀ᵐ x ∂vol n X.z, ∀ i, (hv : M × Fin p → ℂ) (x, i) = hh' (x, i) :=
    ae_all_iff.2 fun i => ae_slice_prodFin n X.z hz p hae'v i
  have hhol : ∀ i, Holo n X.z (fun x => hh' (x, i)) := (holo_prodFin_iff n X.z hz p hh').1 hhol'
  have hSh : Holo n X.z (fun x => ∑ i, g i x * hh' (x, i)) :=
    holo_finsum n X.z _ fun i => Holo.mul n X.z _ _ (hg i) (hhol i)
  have hGS : (G hv : M → ℂ) =ᵐ[vol n X.z] fun x => ∑ i, g i x * hh' (x, i) := by
    filter_upwards [hG hv, hslice] with x h1 h2
    rw [h1]; exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  have hGQ : G hv ∈ Q := ⟨_, hSh, (hl2.1 _).2 hGS⟩
  have hGf : G hv = fL := by
    have h1 := hhG (G hv - fL) (Q.sub_mem hGQ hfLQ)
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      Submodule.coe_subtype] at h1
    rw [← sub_eq_zero, ← inner_sub_right] at h1
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)
  have hfS : ∀ x, f x = ∑ i, g i x * hh' (x, i) := by
    have hae : ∀ᵐ x ∂vol n X.z, f x = ∑ i, g i x * hh' (x, i) := by
      filter_upwards [hGS, hfL] with x h1 h2
      rw [← h2, ← hGf, h1]
    have hSc : Continuous fun x => ∑ i, g i x * hh' (x, i) :=
      Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hSh)
    by_contra hne
    obtain ⟨x0, hx0⟩ := not_forall.1 hne
    have hpos := volOpenPos n M X.z hz _ (isOpen_ne_fun hfc hSc) ⟨x0, hx0⟩
    rw [ae_iff] at hae
    exact hpos.ne' hae
  have hh'c : Continuous hh' := Smooth.continuous n _ hz' _ (Holo.smooth n _ _ hhol')
  have hmeas : ∀ i, Measurable fun x =>
      ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) := fun i =>
    (ENNReal.continuous_ofReal.comp (((hh'c.comp (continuous_id.prodMk continuous_const)).norm.pow 2).mul
      (Real.continuous_exp.comp hφc.neg))).measurable
  refine ⟨fun i x => hh' (x, i), hhol, hfS, ?_⟩
  beta_reduce
  calc ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh' (x, i)‖ ^ 2) * (∑ i, ‖g i x‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 x)) ∂vol n X.z
        = ∑ i, ∫⁻ x, ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) ∂vol n X.z := by
        rw [← lintegral_finsetSum _ (fun i _ => hmeas i)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        congr 1
        rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x),
          Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [skW]; ring
    _ = wint n (fun q : M × Fin p => X.z q.1) hh' (fun x => skW g ph0 t x.1) := by
        unfold wint
        have hm : Measurable fun q : M × Fin p =>
            ENNReal.ofReal (‖hh' q‖ ^ 2 * Real.exp (-skW g ph0 t q.1)) :=
          (ENNReal.continuous_ofReal.comp
            ((hh'c.norm.pow 2).mul (Real.continuous_exp.comp hψ₁c.neg))).measurable
        rw [lintegral_vol_prodFin n X.z hz p _ hm]
    _ = wint n (fun q : M × Fin p => X.z q.1) hv (fun x => skW g ph0 t x.1) := by
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hae'v] with q hq; rw [hq])
    _ = ENNReal.ofReal (‖hv‖ ^ 2) := by
        rw [(hl1.2.1 hv).2, ENNReal.ofReal_toReal (hl1.2.1 hv).1.ne]
    _ ≤ ENNReal.ofReal (t / (t - ((p : ℝ) - 1)) * ‖fL‖ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hci : t / (t - ((p : ℝ) - 1)) = c⁻¹ := by rw [hcdef, inv_div]
        rw [hci, ← div_eq_inv_mul, le_div_iff₀ hc]
        linarith [hhn']
    _ = ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
        rw [ENNReal.ofReal_mul (div_nonneg ht0.le (by linarith)), (hl2.2.1 fL).2,
          ENNReal.ofReal_toReal (hl2.2.1 fL).1.ne]
        congr 1
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hfL] with x hx; rw [hx])
    _ = _ := by rw [hAeq]

end ReciprocityTheory.L2DbarEstimates.H
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply =====
