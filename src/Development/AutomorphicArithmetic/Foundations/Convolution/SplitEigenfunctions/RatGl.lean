import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.UnipotentInvariants.IntegralTsumRowSectionEqZeroOfConstantTermEqZero
import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsEquivRowSelectionUnitsIsotropicVectors
import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsUnipotentInvariantSetUniqueRowScaling

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

variable {E : Type} [Field E] [NumberField E]

private theorem isClosed_vle {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsClosed {p : K × K | (Valued.v p.2 : Γ) ≤ Valued.v p.1} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  have hp' : (Valued.v p.1 : Γ) < Valued.v p.2 := not_le.1 hp
  have hne : (Valued.v p.2 : Γ) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  have hB : IsOpen {x : K | (Valued.v x : Γ) < Valued.v p.2} := by
    have := Valued.isOpen_ball K (Valued.v.restrict p.2)
    simpa only [Valuation.restrict_lt_iff] using this
  have hN : ({x : K | (Valued.v x : Γ) < Valued.v p.2} ×ˢ {y : K | (Valued.v y : Γ) = Valued.v p.2}) ∈ 𝓝 p :=
    prod_mem_nhds (hB.mem_nhds hp') (Valued.locally_const hne)
  filter_upwards [hN] with q hq
  have h1 : (Valued.v q.1 : Γ) < Valued.v p.2 := hq.1
  have h2 : (Valued.v q.2 : Γ) = Valued.v p.2 := hq.2
  show ¬ (Valued.v q.2 : Γ) ≤ Valued.v q.1
  rw [h2]
  exact not_le.2 h1

private def pI (h : G1 E) (v : InfinitePlace E) : v.Completion :=
  if ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ then (h 1 0).1 v else (h 1 1).1 v

private def pF (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E :=
  if Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) then (h 1 0).2 w else (h 1 1).2 w

private theorem det_eq (h : G1 E) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  have := h.2
  rwa [Matrix.det_fin_two] at this

private theorem det_I (h : G1 E) (v : InfinitePlace E) :
    (h 0 0).1 v * (h 1 1).1 v - (h 0 1).1 v * (h 1 0).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (det_eq h)

private theorem det_F (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    (h 0 0).2 w * (h 1 1).2 w - (h 0 1).2 w * (h 1 0).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (det_eq h)

private theorem pI_ne (h : G1 E) (v : InfinitePlace E) : pI h v ≠ 0 := by
  unfold pI
  split_ifs with hc
  · intro h0
    rw [h0, norm_zero] at hc
    have hd : (h 1 1).1 v = 0 := norm_le_zero_iff.1 hc
    have := det_I h v
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, norm_zero] at hc
    exact hc (norm_nonneg _)

private theorem pF_ne (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : pF h w ≠ 0 := by
  unfold pF
  split_ifs with hc
  · intro h0
    rw [h0, map_zero] at hc
    have hd : (h 1 1).2 w = 0 := (map_eq_zero _).1 (le_zero_iff.1 hc)
    have := det_F h w
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, map_zero] at hc
    exact hc zero_le'

private theorem pF_one (h : G1 E) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, Valued.v (pF h w) = 1 := by
  filter_upwards [(h 0 0).2.2, (h 0 1).2.2, (h 1 0).2.2, (h 1 1).2.2] with w ha hb hc hd
  have ha' : Valued.v ((h 0 0).2 w) ≤ 1 := ha
  have hb' : Valued.v ((h 0 1).2 w) ≤ 1 := hb
  have hc' : Valued.v ((h 1 0).2 w) ≤ 1 := hc
  have hd' : Valued.v ((h 1 1).2 w) ≤ 1 := hd
  have hmax : ¬ (Valued.v ((h 1 0).2 w) < 1 ∧ Valued.v ((h 1 1).2 w) < 1) := by
    rintro ⟨h1, h2⟩
    have e1 : Valued.v ((h 0 0).2 w * (h 1 1).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha') h2
    have e2 : Valued.v ((h 0 1).2 w * (h 1 0).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb') h1
    have := Valuation.map_sub_lt _ e1 e2
    rw [det_F h w, map_one] at this
    exact lt_irrefl _ this
  unfold pF
  split_ifs with hle
  · by_contra hne
    exact hmax ⟨lt_of_le_of_ne hc' hne, lt_of_le_of_lt hle (lt_of_le_of_ne hc' hne)⟩
  · by_contra hne
    exact hmax ⟨lt_of_lt_of_le (not_le.1 hle) hd', lt_of_le_of_ne hd' hne⟩

private def bF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨pF h, (pF_one h).mono fun w hw => (le_of_eq hw : Valued.v (pF h w) ≤ 1)⟩

private def cF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => (pF h w)⁻¹, (pF_one h).mono fun w hw =>
    (le_of_eq (by rw [map_inv₀, hw, inv_one]) : Valued.v (pF h w)⁻¹ ≤ 1)⟩

private def al (h : G1 E) : IdeleGroup E where
  val := (fun v => (pI h v)⁻¹, cF h)
  inv := (fun v => pI h v, bF h)
  val_inv := Prod.ext (funext fun v => inv_mul_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => inv_mul_cancel₀ (pF_ne h w))
  inv_val := Prod.ext (funext fun v => mul_inv_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => mul_inv_cancel₀ (pF_ne h w))

private def co (x : IdeleGroup E) :
    (∀ v : InfinitePlace E, v.Completion) × (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) :=
  (((x⁻¹ : IdeleGroup E) : A E).1, fun w => ((x⁻¹ : IdeleGroup E) : A E).2 w)

private theorem continuous_co : Continuous (co : IdeleGroup E → _) := by
  have h0 : Continuous fun x : IdeleGroup E => ((x⁻¹ : IdeleGroup E) : A E) :=
    Units.continuous_val.comp continuous_inv
  refine Continuous.prodMk (continuous_fst.comp h0) (continuous_pi fun w => ?_)
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp h0)

private theorem injective_co : Function.Injective (co : IdeleGroup E → _) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  apply inv_injective
  apply Units.ext
  exact Prod.ext h1 (Subtype.ext <| funext fun w => congrFun h2 w)

private theorem cont_e (i j : Fin 2) : Continuous fun h : G1 E => (h i j : A E) :=
  Continuous.matrix_elem continuous_subtype_val i j

private theorem cont_I (i j : Fin 2) (v : InfinitePlace E) : Continuous fun h : G1 E => (h i j).1 v :=
  (continuous_apply v).comp (continuous_fst.comp (cont_e i j))

private theorem cont_F (i j : Fin 2) (w : HeightOneSpectrum (𝓞 E)) : Continuous fun h : G1 E => (h i j).2 w :=
  (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp (cont_e i j))

private theorem measurable_al : Measurable (al : G1 E → IdeleGroup E) := by
  letI : ∀ v : InfinitePlace E, MeasurableSpace v.Completion := fun _ => borel _
  haveI : ∀ v : InfinitePlace E, BorelSpace v.Completion := fun _ => ⟨rfl⟩
  letI : ∀ w : HeightOneSpectrum (𝓞 E), MeasurableSpace (w.adicCompletion E) := fun _ => borel _
  haveI : ∀ w : HeightOneSpectrum (𝓞 E), BorelSpace (w.adicCompletion E) := fun _ => ⟨rfl⟩
  have hc := comap_eq_borel_of_continuous_injective (continuous_co (E := E)) (injective_co (E := E))
  have hm : Measurable ((co : IdeleGroup E → _) ∘ (al : G1 E → IdeleGroup E)) := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun v => ?_) (measurable_pi_iff.2 fun w => ?_)
    · have hS : MeasurableSet {h : G1 E | ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖} :=
        (isClosed_le (cont_I 1 1 v).norm (cont_I 1 0 v).norm).measurableSet
      exact Measurable.ite hS (cont_I 1 0 v).measurable (cont_I 1 1 v).measurable
    · have hS : MeasurableSet {h : G1 E | Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)} :=
        (isClosed_vle.preimage ((cont_F 1 0 w).prodMk (cont_F 1 1 w))).measurableSet
      exact Measurable.ite hS (cont_F 1 0 w).measurable (cont_F 1 1 w).measurable
  have h2 := measurable_comap_iff.2 hm
  rw [hc, ← BorelSpace.measurable_eq] at h2
  exact h2

private theorem e_nU (u : A E) (h : G1 E) (j : Fin 2) : (nU u * h) 1 j = h 1 j := by
  show ((nU u).1 * h.1) 1 j = h.1 1 j
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e_mD (t : (A E)ˣ) (h : G1 E) (j : Fin 2) :
    (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := by
  show ((mD t).1 * h.1) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h.1 1 j
  simp [mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem al_nU (u : A E) (h : G1 E) : al (nU u * h) = al h := by
  have hI : pI (nU u * h) = pI h := by
    funext v
    simp only [pI, e_nU]
  have hF : pF (nU u * h) = pF h := by
    funext w
    simp only [pF, e_nU]
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (nU u * h) v)⁻¹ = (pI h v)⁻¹
    rw [hI]
  · show (pF (nU u * h) w)⁻¹ = (pF h w)⁻¹
    rw [hF]

private theorem tI (t : (A E)ˣ) (v : InfinitePlace E) :
    ((t⁻¹ : (A E)ˣ) : A E).1 v * (t : A E).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (Units.inv_mul t)

private theorem tF (t : (A E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((t⁻¹ : (A E)ˣ) : A E).2 w * (t : A E).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (Units.inv_mul t)

private theorem pI_mD (t : (A E)ˣ) (h : G1 E) (v : InfinitePlace E) :
    pI (mD t * h) v = ((t⁻¹ : (A E)ˣ) : A E).1 v * pI h v := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).1 v ≠ 0 := left_ne_zero_of_mul_eq_one (tI t v)
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).1 v = ((t⁻¹ : (A E)ˣ) : A E).1 v * (h 1 j).1 v := fun j => by rw [e j]; rfl
  have key : ‖((mD t * h) 1 1).1 v‖ ≤ ‖((mD t * h) 1 0).1 v‖ ↔ ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ := by
    rw [e', e', norm_mul, norm_mul]
    exact mul_le_mul_iff_of_pos_left (norm_pos_iff.2 hs)
  unfold pI
  by_cases hc : ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem pF_mD (t : (A E)ˣ) (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    pF (mD t * h) w = ((t⁻¹ : (A E)ˣ) : A E).2 w * pF h w := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).2 w ≠ 0 := left_ne_zero_of_mul_eq_one (tF t w)
  have hs' : Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w) ≠ 0 := (Valuation.ne_zero_iff _).2 hs
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).2 w = ((t⁻¹ : (A E)ˣ) : A E).2 w * (h 1 j).2 w := fun j => by rw [e j]; rfl
  have key : Valued.v (((mD t * h) 1 1).2 w) ≤ Valued.v (((mD t * h) 1 0).2 w) ↔
      Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) := by
    rw [e', e', map_mul, map_mul]
    constructor
    · intro x
      have := mul_le_mul_right x (Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w))⁻¹
      simpa [inv_mul_cancel_left₀ hs'] using this
    · intro x
      exact mul_le_mul_right x _
  unfold pF
  by_cases hc : Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem al_mD (t : (A E)ˣ) (h : G1 E) : al (mD t * h) = t * al h := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (mD t * h) v)⁻¹ = (t : A E).1 v * (pI h v)⁻¹
    rw [pI_mD, mul_inv, inv_eq_of_mul_eq_one_right (tI t v)]
  · show (pF (mD t * h) w)⁻¹ = (t : A E).2 w * (pF h w)⁻¹
    rw [pF_mD, mul_inv, inv_eq_of_mul_eq_one_right (tF t w)]

end UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.torCo :
    TorCo := by
  intro E _ _
  exact ⟨al, measurable_al, al_nU, al_mD⟩
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem om_L {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ)
    {h : GL (Fin 2) (A E)} (hn : nu ℚ h = 1) (v : V4 ℚ) :
    (W.Om g (W.L h ph)).1 v = (W.Om g ph).1 (D.act h⁻¹ v) := by
  have hc := W.comm h g
  rw [hn, M.cD_one] at hc
  have h1 : W.Om g (W.L h ph) = W.L h (W.Om g ph) := (congrArg (fun T => T ph) hc).symm
  rw [h1, W.L_apply, hn, M.ab_one]
  simp

private theorem rat_gl {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  apply Units.ext; rfl

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rank1 :
    DecE → Maj → Orb1 → Rank1 := by
  intro hD hM hO E _ _ _ D W M₀ N P ph hph φ hφ g y hy
  obtain ⟨hLf, hcus, -⟩ := hD E P φ hφ
  obtain ⟨b0, a0, k0, hk0, hg⟩ := M.iwa ℚ g
  obtain ⟨B, hB⟩ := hM E D W M₀ N P ph hph φ hφ {y} isCompact_singleton (by simpa using hy) (ab a0) (M.ab_pos a0) 0
  have hb : ∀ h : G1 E, Summable (fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a0 ^ 2 := by
    intro h
    obtain ⟨h1, h2, -⟩ := hB b0 a0 k0 hk0 le_rfl h y rfl
    rw [hg]
    exact ⟨h1, h2⟩
  obtain ⟨⟨σ, hσ⟩, -⟩ := M.rowCosets E
  obtain ⟨T, hTm, hTn, hTs⟩ := UpperTheory.exists_unipotentInvariant_set_unique_row_scaling torCo E
  have glm : ∀ a b : G1 E, gl (a * b) = gl a * gl b := fun a b => map_mul Matrix.SpecialLinearGroup.toGL a b
  have hnu : ∀ x : G1 E, nu ℚ (gl x * y) = 1 := fun x => by rw [nu_mul, nu_gl, hy, one_mul]
  set F : G1 E → (Fin 4 → ℚ) → ℂ := fun x ξ => (W.Om g (W.L (gl x * y) ph)).1 (rp ξ) with hF
  have hFe : ∀ x ξ, F x ξ = (W.Om g ph).1 (D.act (gl x * y)⁻¹ (rp ξ)) := fun x ξ => om_L W g ph (hnu x) _
  have hFc : ∀ ξ, Continuous fun x => F x ξ := by
    intro ξ
    simp only [hFe]
    have h1 : Continuous fun x : G1 E => (gl x * y)⁻¹ := (M.continuous_gl.mul continuous_const).inv
    have h2 := D.continuous_act' h1 (continuous_const (y := rp ξ))
    exact ((W.cont (ph)).comp (continuous_const (y := g) |>.prodMk h2))
  have hinj : Function.Injective fun s : ℚˣ => (![0, (s : ℚ), 0, 0] : Fin 4 → ℚ) := by
    intro s s' h
    exact Units.ext (by simpa using congrFun h 1)
  have hsu : ∀ x, Summable fun s : ℚˣ => F x ![0, (s : ℚ), 0, 0] := fun x =>
    ((hb x).1.comp_injective hinj).of_norm
  set u : G1 E → ℂ := fun x => ∑' s : ℚˣ, F x ![0, (s : ℚ), 0, 0] with hu
  have hum : Measurable u := by
    refine measurable_of_tendsto_metrizable' (u := atTop) (f := fun (S : Finset ℚˣ) x => ∑ s ∈ S, F x ![0, (s : ℚ), 0, 0])
      (fun S => Finset.measurable_sum _ fun s _ => (hFc _).measurable) (tendsto_pi_nhds.2 fun x => (hsu x).hasSum)
  have hun : ∀ b x, u (nU b * x) = u x := by
    intro b x
    refine tsum_congr fun s => ?_
    have h5 := (hO E D).2.2.2.2 (-b) s
    have h6 : (gl (nU b))⁻¹ = gl (nU (-b)) := by rw [M.nU_neg]; exact (map_inv Matrix.SpecialLinearGroup.toGL (nU b)).symm
    rw [hFe, hFe, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul, h6, h5]
  set Aa : G1 E → ℂ := T.indicator u with hA
  set c : G1 E → ℂ := fun x => φ.1 (gl x * y) with hc
  have hAm : Measurable Aa := hum.indicator hTm
  have hcm : Measurable c := (hLf.1.comp (M.continuous_gl.mul continuous_const)).measurable
  have hAn : ∀ b x, Aa (nU b * x) = Aa x := by
    intro b x
    by_cases hx : x ∈ T
    · rw [hA, Set.indicator_of_mem hx, Set.indicator_of_mem ((hTn b x).2 hx), hun]
    · rw [hA, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hTn b x).1 h))]
  have hcl : ∀ γ x, c (ratS E γ * x) = c x := by
    intro γ x
    change φ.1 (gl (ratS E γ * x) * y) = φ.1 (gl x * y)
    rw [glm, rat_gl, mul_assoc]
    exact hLf.2 _ _
  have h0 : ∀ x, ∫ b in fundamentalSet E, c (nU b * x) ∂(adeleMeasure E) = 0 := by
    intro x
    have := hcus (gl x * y)
    simpa only [hc, glm, mul_assoc] using this
  have hact : ∀ (x : G1 E) (γ : Matrix.SpecialLinearGroup (Fin 2) E) (ξ ξ' : Fin 4 → ℚ),
      rp ξ' = D.act (gl (ratS E γ))⁻¹ (rp ξ) → F (ratS E γ * x) ξ = F x ξ' := by
    intro x γ ξ ξ' h
    rw [hFe, hFe, h, glm, mul_assoc, _root_.mul_inv_rev, Dat.act_mul]
  have hSel : ∀ x, ∃ e : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} × ℚˣ ≃ ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0},
      ∀ r s, rp (e (r, s)).1 = D.act (gl (ratS E (σ r.1)))⁻¹ (rp ![0, (s : ℚ), 0, 0]) :=
    fun x => UpperTheory.exists_equiv_rowSelection_units_isotropicVectors D σ _ hO hσ (hTs σ hσ x)
  have hind : ∀ x r, Aa (ratS E (σ r) * x) =
      Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => u (ratS E (σ r) * x)) r := by
    intro x r
    by_cases h : ratS E (σ r) * x ∈ T
    · rw [hA, Set.indicator_of_mem h, Set.indicator_of_mem (show r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
    · rw [hA, Set.indicator_of_notMem h, Set.indicator_of_notMem (show r ∉ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} from h)]
  have hTh : ∀ x, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 = ∑' r, Aa (ratS E (σ r) * x) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have hs0 : Summable fun ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0} => F x ξ.1 :=
      ((hb x).1.comp_injective Subtype.val_injective).of_norm
    have hs : Summable fun p => F x (e p).1 := e.summable_iff.2 hs0
    change ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, F x ξ.1 = _
    rw [← e.tsum_eq (fun ξ => F x ξ.1), hs.tsum_prod]
    simp_rw [hind]
    rw [← tsum_subtype]
    refine tsum_congr fun r => tsum_congr fun s => ?_
    exact (hact x (σ r.1) _ _ (he r s)).symm
  have hbd : ∀ x, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := by
    intro x
    obtain ⟨e, he⟩ := hSel x
    have h1 : ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := by
      calc ∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ
          = ∑' r, Set.indicator {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T} (fun r => ‖u (ratS E (σ r) * x)‖ₑ) r := by
            refine tsum_congr fun r => ?_
            rw [hind]
            by_cases h : r ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
        _ = ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ‖u (ratS E (σ r.1) * x)‖ₑ :=
            (tsum_subtype _ (fun r => ‖u (ratS E (σ r) * x)‖ₑ)).symm
        _ ≤ ∑' r : ↥{r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, ∑' s : ℚˣ, ‖F x (e (r, s)).1‖ₑ := by
            refine ENNReal.tsum_le_tsum fun r => enorm_tsum_le_tsum_enorm.trans_eq (tsum_congr fun s => ?_)
            rw [hact x (σ r.1) _ _ (he r s)]
        _ = ∑' p, ‖F x (e p).1‖ₑ := ENNReal.tsum_prod.symm
        _ = ∑' ξ : ↥{ξ : Fin 4 → ℚ | ξ ≠ 0 ∧ qr D.δ ξ = 0}, ‖F x ξ.1‖ₑ := e.tsum_eq fun ξ => ‖F x ξ.1‖ₑ
        _ ≤ ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    have h2 : ∑' ξ : Fin 4 → ℚ, ‖F x ξ‖ₑ = ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb x).1]
      exact tsum_congr fun ξ => (ofReal_norm_eq_enorm _).symm
    calc ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ = (∑' r, ‖Aa (ratS E (σ r) * x)‖ₑ) * ‖c x‖ₑ := by
          simp only [enorm_mul]; exact ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖ₑ := by rw [← h2]; gcongr
      _ = ENNReal.ofReal ((∑' ξ : Fin 4 → ℚ, ‖F x ξ‖) * ‖c x‖) := by
          rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ ENNReal.ofReal (B * ab a0 ^ 2) := ENNReal.ofReal_le_ofReal (hb x).2
  have hfin : (∫⁻ x in N.D, ∑' r, ‖Aa (ratS E (σ r) * x) * c x‖ₑ ∂N.μ) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hbd) ?_)
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volE E N)
  have hz := UpperTheory.integral_tsum_rowSection_eq_zero_of_constantTerm_eq_zero N σ Aa c hσ hAm hcm hAn hcl h0 hfin
  change ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl x * y) ph)).1 * c x = ∑' r, Aa (ratS E (σ r) * x) * c x
  rw [hTh, tsum_mul_right]
end
