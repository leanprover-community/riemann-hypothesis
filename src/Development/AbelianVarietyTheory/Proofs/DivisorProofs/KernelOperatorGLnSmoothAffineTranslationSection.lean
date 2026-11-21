import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
import BuildAid.ForwardExisting

section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rapid_superposition_characters' : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  first | exact @GlobalTheory.JSW.exists_rapid_superposition_characters | exact GlobalTheory.JSW.exists_rapid_superposition_characters | (intros; apply GlobalTheory.JSW.exists_rapid_superposition_characters <;> assumption)
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (exact GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth  <;> assumption)
end

section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem measurable_htInf_comp {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun x => htInf (γ x) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isKerOpInf_comp_rapidFamInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η →
    ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ),
    (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) →
    (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) →
    IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  intro E _ _ n Z _ _ _ T hT X _ ν _ k γ η hfam S t χ hS hSk
  obtain ⟨X₀, m₀, ν₀, hν₀, k₀, γ₀, η₀, ⟨hk₀, hγ₀, hη₀, hint₀⟩, hT⟩ := hT
  obtain ⟨hγ, hjoint, hmom⟩ := hfam
  obtain ⟨hkj, hηj⟩ := hjoint X₀ γ₀ hγ₀
  have mη₀ : Measurable η₀ := measurable_dual hη₀
  have mηj : Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 := measurable_dual hηj
  have mht : Measurable fun x => htInf (γ x) := measurable_htInf_comp hγ
  have hrap : IsRapidFInf (ν₀.prod ν) (fun p : X₀ × X => k₀ p.1 * k (γ₀ p.1) p.2) (fun p => γ p.2)
      (fun p => η₀ p.1 + η (γ₀ p.1) p.2) := by
    refine ⟨(hk₀.comp measurable_fst).mul hkj, fun i j => (hγ i j).comp measurable_snd,
      fun z => ((hη₀ z).comp measurable_fst).add (hηj z), fun N => ?_⟩
    obtain ⟨C, M, hCM⟩ := hmom N
    let F : X₀ × X → ℝ := fun p => (‖k₀ p.1‖ * (1 + ‖η₀ p.1‖) ^ N) *
      (‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N)
    have mF : Measurable F := by
      have a1 : Measurable fun p : X₀ × X => k₀ p.1 := hk₀.comp measurable_fst
      have a2 : Measurable fun p : X₀ × X => η₀ p.1 := mη₀.comp measurable_fst
      have a3 : Measurable fun p : X₀ × X => htInf (γ p.2) := mht.comp measurable_snd
      exact (a1.norm.mul ((measurable_const.add a2.norm).pow_const N)).mul
        (hkj.norm.mul ((a3.mul (measurable_const.add mηj.norm)).pow_const N))
    have F0 : ∀ p, 0 ≤ F p := fun p => by
      have := htInf_pos' (γ p.2)
      positivity
    have hF : Integrable F (ν₀.prod ν) := by
      rw [integrable_prod_iff mF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun x₀ => ((hCM (γ₀ x₀)).1.const_mul (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N)), ?_⟩
      refine ((hint₀ (max N M)).const_mul (max C 0)).mono'
        (mF.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Filter.Eventually.of_forall fun x₀ => ?_)
      have e1 : ∫ y, ‖F (x₀, y)‖ ∂ν = (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N) *
          ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (F0 _))
      have I0 : 0 ≤ ∫ y, ‖F (x₀, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg I0, e1]
      have hq := (hCM (γ₀ x₀)).2
      have A0 : 0 ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N := by positivity
      have h1 : 1 ≤ htInf (γ₀ x₀) := le_of_eq_of_le rfl (by
        unfold htInf
        calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _)
      have h2 : (1 : ℝ) ≤ 1 + ‖η₀ x₀‖ := by linarith [norm_nonneg (η₀ x₀)]
      have p1 : (1 + ‖η₀ x₀‖) ^ N ≤ (1 + ‖η₀ x₀‖) ^ max N M := pow_le_pow_right₀ h2 (le_max_left _ _)
      have p2 : htInf (γ₀ x₀) ^ M ≤ htInf (γ₀ x₀) ^ max N M := pow_le_pow_right₀ h1 (le_max_right _ _)
      have hm : C * htInf (γ₀ x₀) ^ M ≤ max C 0 * htInf (γ₀ x₀) ^ max N M :=
        mul_le_mul (le_max_left _ _) p2 (by positivity) (le_max_right _ _)
      calc ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν
          ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * (max C 0 * htInf (γ₀ x₀) ^ max N M) :=
            mul_le_mul_of_nonneg_left (hq.trans hm) A0
        _ ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ max N M * (max C 0 * htInf (γ₀ x₀) ^ max N M) := by
            gcongr
        _ = max C 0 * (‖k₀ x₀‖ * (htInf (γ₀ x₀) * (1 + ‖η₀ x₀‖)) ^ max N M) := by rw [mul_pow]; ring
    refine hF.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((hk₀.comp measurable_fst).mul hkj).norm.mul (((mht.comp measurable_snd).mul
        (measurable_const.add ((mη₀.comp measurable_fst).add mηj).norm)).pow_const N)).aestronglyMeasurable
    · have hh := htInf_pos' (γ p.2)
      have hb : htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖) ≤
          (1 + ‖η₀ p.1‖) * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) := by
        have := mul_le_mul_of_nonneg_left (show 1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖ ≤ (1 + ‖η₀ p.1‖) * (1 + ‖η (γ₀ p.1) p.2‖) by
          nlinarith [norm_add_le (η₀ p.1) (η (γ₀ p.1) p.2), norm_nonneg (η₀ p.1), norm_nonneg (η (γ₀ p.1) p.2),
            mul_nonneg (norm_nonneg (η₀ p.1)) (norm_nonneg (η (γ₀ p.1) p.2))]) hh.le
        linarith
      have hp : (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N ≤
          (1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N :=
        (pow_le_pow_left₀ (by positivity) hb N).trans_eq (mul_pow _ _ _)
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N
          ≤ ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ *
              ((1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = F p := by simp only [F]; ring
  refine ⟨X₀ × X, inferInstance, ν₀.prod ν, inferInstance, _, _, _, hrap, ?_⟩
  intro W hW z g
  have hint := hrap.integrable hW z g
  show χ z * T (S W) z (g * t z) = _
  rw [integral_prod _ hint, hT (S W) (hS W hW) z (g * t z), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
  simp only
  rw [show χ z * (k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * S W (g * t z * γ₀ x₀)) =
      k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * (χ z * S W (g * t z * γ₀ x₀)) by ring, hSk W hW (γ₀ x₀) z g,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.add_apply, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

example : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := isKerOpInf_comp_rapidFamInf

end GlobalTheory.JSW.MirCinf
end
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ), ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  first | (exact @GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (exact GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (intros; apply GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf  <;> assumption)
end

section
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_affine_family_eq_integral_kernel : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  atlas_forward_decl GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf
end

section
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_rapid_superposition_characters' _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.smoothing_affine_family_eq_integral_kernel E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  atlas_forward_decl GlobalTheory.JSW.MirCinf.kerOpInf_section
end
