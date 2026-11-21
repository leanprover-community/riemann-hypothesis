import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
import Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatRowLintegralAbsPowBounded

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma inv_mem_UU' {t : (A ℚ)ˣ} (ht : t ∈ UU) : t⁻¹ ∈ UU := by
  refine ⟨?_, fun v => ?_⟩
  · have h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1 := congrArg Prod.fst (Units.mul_inv t)
    rw [ht.1, one_mul] at h
    exact h
  · have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, ht.2 v, one_mul, map_one] at this

private lemma cD_mem_KK {t : (A ℚ)ˣ} (ht : t ∈ UU) {k : G1 ℚ} (hk : k ∈ KK ℚ) : cD t k ∈ KK ℚ := by
  have hi := inv_mem_UU' ht
  have fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have c00 : (cD t k) 0 0 = k 0 0 := rfl
  have c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ) := rfl
  have c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0 := rfl
  have c11 : (cD t k) 1 1 = k 1 1 := rfl
  have e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg Prod.fst c00
    · show ((cD t k) 0 1).1 = (k 0 1).1
      rw [c01, fm, hi.1, mul_one]
    · show ((cD t k) 1 0).1 = (k 1 0).1
      rw [c10, fm, ht.1, one_mul]
    · exact congrArg Prod.fst c11
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have h := hk.1 i j
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    have e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 →
        (a * b + c * d).1 = (a' * b' + c' * d').1 := by
      intro a b c d a' b' c' d' h1 h2 h3 h4
      rw [fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]
    exact e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)
  · have ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (ht.2 v).le
    have tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (hi.2 v).le
    fin_cases i <;> fin_cases j
    · exact hk.2 v 0 0
    · show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c01]
      exact mul_mem (hk.2 v 0 1) tj
    · show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c10]
      exact mul_mem ti (hk.2 v 1 0)
    · exact hk.2 v 1 1

theorem UpperTheory.maximalCompact_measure_map_conjDiag_eq :
    ∀ (M₀ : Meas ℚ) (t : IdeleGroup ℚ), t ∈ UU → M₀.κ.map (cD t) = M₀.κ := by
  intro m t ht
  haveI := m.prob
  have hm : Measurable (cD t : G1 ℚ → G1 ℚ) := (M.continuous_cD t).measurable
  have hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ := by
    rw [ae_iff]
    exact m.supp
  have right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_right k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  have left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_left k hk]
    rw [lintegral_map hf (measurable_const_mul k)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm]
  have hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2)) :=
    hf.comp (measurable_fst.mul (hm.comp measurable_snd))
  have hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    have h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ :=
      hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  have hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
    have h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
      refine hae.mono fun x hx => ?_
      have hk : cD t⁻¹ x ∈ KK ℚ := cD_mem_KK (inv_mem_UU' ht) hx
      have ex : x = cD t (cD t⁻¹ x) := by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      have e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y) := by
        intro y
        rw [Function.comp_apply, M.cD_mul, ← ex]
      simp only [e]
      exact left (f ∘ cD t) (hf.comp hm) _ hk
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  rw [← hB, ← hA]
  exact lintegral_lintegral_swap hF.aemeasurable
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact :
    ∀ (M₀ : Meas ℚ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        MeasurePreserving (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) M₀.ν M₀.ν ∧
        MeasurableEmbedding (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) := by
  intro M₀ t u hu
  haveI := M₀.prob
  let c : IdeleGroup ℚ := (iy (Real.exp t) * u : (A ℚ)ˣ)
  have h1 : MeasurePreserving (fun z : IdeleGroup ℚ => c * z⁻¹) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    (measurePreserving_mul_left (ideleMeasure ℚ) c).comp (Measure.measurePreserving_inv (ideleMeasure ℚ))
  have h2 : MeasurePreserving (cD u : G1 ℚ → G1 ℚ) M₀.κ M₀.κ :=
    ⟨(M.continuous_cD u).measurable, UpperTheory.maximalCompact_measure_map_conjDiag_eq M₀ u hu⟩
  let e1 : IdeleGroup ℚ ≃ᵐ IdeleGroup ℚ := (MeasurableEquiv.inv (IdeleGroup ℚ)).trans (MeasurableEquiv.mulLeft c)
  let e2 : G1 ℚ ≃ᵐ G1 ℚ :=
    { toFun := cD u
      invFun := cD (u⁻¹ : (A ℚ)ˣ)
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      measurable_toFun := (M.continuous_cD u).measurable
      measurable_invFun := (M.continuous_cD _).measurable }
  exact ⟨h1.prod h2, (e1.prodCongr e2).measurableEmbedding⟩
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem row_nU (b : A ℚ) (g : G1 ℚ) (u : (A ℚ)ˣ) (j : Fin 2) :
    (gl (nU b * g) * dM u).val 1 j = (gl g * dM u).val 1 j := by
  rw [Units.val_mul, Units.val_mul, M.val_gl, M.val_gl, M.val_mul]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem row_mD (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a * cD u k) * dM u).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * G.row k j := by
  have h : gl (mD a * cD u k) = gl (mD a) * gl (cD u k) := map_mul _ _ _
  rw [h, mul_assoc, M.gl_cD, Units.val_mul, Units.val_mul, M.val_gl, M.val_gl]
  simp [mD, dM, G.row, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Matrix.vecMul, dotProduct]

theorem UpperTheory.maximalCompact_integral_unipotent_norm_finite :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        (_root_.UpperTheory.ConvolutionTheory.R2.M.J0 M₀ fun g => ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ)) ≠ ⊤ := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨B, hB⟩ := hA.bdd
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  obtain ⟨C, hC⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ 2 (by norm_num)
  obtain ⟨-, hiy, -, hU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  haveI := M₀.prob
  have hw : ∀ g : G1 ℚ, ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ) ≤
      ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ := by
    intro g
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ)
      fun b => ?_).trans ?_
    · simp only [Un.Uu, row_nU, enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  let F : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 : ℝ))
  have hF : Measurable F := by
    have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j :=
      (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
        (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
    have h2 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => ab p.1 ^ (2 : ℝ) :=
      (M.continuous_ab.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
    exact h1.measurable.enorm.mul h2.measurable.ennreal_ofReal
  have hI : ∫⁻ p, F p ∂M₀.ν ≤ C := by
    rw [Meas.ν, lintegral_prod_symm _ hF.aemeasurable]
    have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
      rw [ae_iff]
      exact M₀.supp
    refine (lintegral_mono_ae (g := fun _ => (C : ℝ≥0∞)) (hae.mono fun k hk => hC k hk)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  unfold M.J0
  rw [← hmp.lintegral_comp_emb hme]
  have hK : ENNReal.ofReal B * ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK (ENNReal.coe_ne_top (r := C))) ?_
  refine le_trans ?_ (mul_le_mul_right hI _)
  rw [← lintegral_const_mul _ hF]
  refine lintegral_mono fun p => ?_
  refine (mul_le_mul_right (hw _) _).trans (le_of_eq ?_)
  have e1 : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1) * cD u p.2) * dM u).val 1 j) =
      fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j := by
    funext j
    rw [row_mD, ← mul_assoc, ← Units.val_mul]
    have : (iy (Real.exp t) * ((Un.aa t u p.1)⁻¹ * u) : (A ℚ)ˣ) = p.1 := by
      have h : ∀ x y z : (A ℚ)ˣ, x * ((x * y * z⁻¹)⁻¹ * y) = z := fun x y z => by
        rw [mul_left_comm, ← mul_assoc, mul_right_comm, mul_comm x y, mul_assoc _ y x, mul_comm y x, mul_inv, inv_inv,
          mul_right_comm, inv_mul_cancel, one_mul]
      exact h _ _ _
    rw [this]
  have e2 : M.wt (Un.aa t u p.1) = ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) * ENNReal.ofReal (ab p.1 ^ (2 : ℝ)) := by
    have h : ab (Un.aa t u p.1) = Real.exp t * (ab p.1)⁻¹ := by
      have h0 : ab (Un.aa t u p.1) = ab (iy (Real.exp t)) * ab u * ab (p.1⁻¹ : (A ℚ)ˣ) := by
        rw [← M.ab_mul, ← M.ab_mul]
        rfl
      rw [h0, hiy _ (Real.exp_ne_zero t), hU u hu, M.ab_inv, abs_of_pos (Real.exp_pos t), mul_one]
    rw [M.wt, h, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two, mul_inv, inv_inv, mul_pow]
  simp only [e1, e2, F]
  ring
end
