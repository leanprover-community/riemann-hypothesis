import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfRealQuotHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero : ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : Y → E), Measurable p → (∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0) → ∀ s : Set E, MeasurableSet s → ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  first | exact @GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | exact GlobalTheory.FourierPush.setIntegral_preimage_eq_zero | (intros; apply GlobalTheory.FourierPush.setIntegral_preimage_eq_zero <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FourierRealPart

variable {D : D7}

theorem exists_section (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ s : (D.what₂.Tau → ℂ) → AE D, Continuous s ∧ (∀ w, finPart D (s w) = 0) ∧
      (∀ w τ, θ τ (infPart D (s w)) = w τ) ∧ (∀ a, infPart D (s fun τ => θ τ (infPart D a)) = infPart D a) ∧
      ∀ τ, Continuous fun a : AE D => θ τ (infPart D a) := by
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig D.what₂.Tau
    (tauE D) θ (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ a : AE D, (e1 a).1 = infPart D a := fun a => (he1 a).1
  have hfin : ∀ a : AE D, (e1 a).2 = finPart D a := fun a => (he1 a).2
  refine ⟨fun w => e1.symm (e.symm w, 0), hc1'.comp (hc'.prodMk continuous_const), fun w => ?_, fun w τ => ?_,
    fun a => ?_, fun τ => ?_⟩
  · rw [← hfin, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply]
    apply e.injective
    funext τ
    rw [RingEquiv.apply_symm_apply, he]
  · have h : (fun a : AE D => θ τ (infPart D a)) = fun a => e (e1 a).1 τ := by
      funext a
      rw [he, hinf]
    rw [h]
    exact (continuous_apply τ).comp (hc.comp (continuous_fst.comp hc1))

theorem dualPt_finPart {T : HSp D} {ρ : ℕ} {b : Mx D ρ T.rank} (hb : b.map (finPart D) = 0) :
    (GlobalTheory.Unf.DoubleSum.dualPt T ρ b).map (finPart D) = 0 := by
  have h : (b ⬝ giA T).map (finPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine GlobalTheory.OrientedChar.finPart_cA_eq_zero (z := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show finPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]

set_option synthInstance.maxHeartbeats 400000 in

theorem psi_dualPt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (z : Mx D W.rank ρ) {b : Mx D ρ W.rank}
    (hb : b.map (finPart D) = 0) :
    ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ τ, ((2 * (∑ i, ∑ j,
        θ τ (infPart D (z i j)) * θ τ (infPart D (b j i))).re : ℝ) : ℂ)) := by
  rw [GlobalTheory.Unf.DoubleSum.symplO_dualPt]
  have hfin : finPart D (z * b).trace = 0 := GlobalTheory.PhaseReal.finPart_trace z b hb
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  have h1 : ψ (Algebra.trace (AF D.host.F) (AE D) (z * b).trace) =
      psiInf D.host.F ψ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) (z * b).trace)) := congrArg ψ hT
  rw [h1, hψ.2.2 θ hθ]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [GlobalTheory.PhaseReal.theta_trace θ hθ τ]
  congr 3
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem linear_expand {K : Type} [Fintype K] [DecidableEq K] (l : (K → ℂ) →L[ℝ] ℝ) (Z : K → ℂ) :
    l Z = ∑ k, ((Z k).re * l (Pi.single k 1) + (Z k).im * l (Pi.single k Complex.I)) := by
  conv_lhs => rw [← Finset.univ_sum_single Z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : Pi.single k (Z k) = (Z k).re • (Pi.single k (1 : ℂ) : K → ℂ) + (Z k).im • (Pi.single k Complex.I : K → ℂ) := by
    ext k'
    by_cases h : k' = k
    · subst h
      simp [Complex.ext_iff]
    · simp [h]
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.FourierRealPart

open GlobalTheory.FourierRealPart in

theorem GlobalTheory.FourierRealPart.integral_preimage_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  intro D ψ hψ V V₀ W ρ d Y _ m F hF x hx hc S hS hsat
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨s, hsc, hsf, hsθ, hsinf, hcθ⟩ := exists_section θ hθ
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  classical
  let P : Mx D W.rank ρ → (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) := fun z k => θ k.2.2 (infPart D (z k.1 k.2.1))
  let sec : (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) → Mx D W.rank ρ := fun w i j => s fun τ => w (i, j, τ)
  have hP : Continuous P :=
    continuous_pi fun k => (hcθ k.2.2).comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  have hsec : Continuous sec :=
    continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun τ => continuous_apply _)
  have hmem : ∀ z, z ∈ S ↔ sec (P z) ∈ S := fun z => hsat _ _ (by
    funext i j
    exact (hsinf (z i j)).symm)
  have hpre : x ⁻¹' S = (P ∘ x) ⁻¹' (sec ⁻¹' S) := by
    ext y
    exact hmem (x y)
  rw [hpre]
  refine GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero Y m F hF _ (P ∘ x) (hP.measurable.comp hx) ?_ _ (hsec.measurable hS)
  intro l
  let B : Fin W.rank × Fin ρ × D.what₂.Tau → ℂ := fun k =>
    ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * ((l (Pi.single k 1) : ℂ) - (l (Pi.single k Complex.I) : ℂ) * Complex.I)
  let b : Mx D ρ W.rank := fun j i => s fun τ => B (i, j, τ)
  have hb : b.map (finPart D) = 0 := by
    funext j i
    exact hsf _
  have key := hc (GlobalTheory.Unf.DoubleSum.dualPt W ρ b) (dualPt_finPart hb)
  have hpt : ∀ z : Mx D W.rank ρ, Complex.exp ((l (P z) : ℂ) * Complex.I) =
      ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) := by
    intro z
    rw [psi_dualPt hψ θ hθ d z hb]
    congr 1
    have hbθ : ∀ i j τ, θ τ (infPart D (b j i)) = B (i, j, τ) := fun i j τ => hsθ _ τ
    simp only [hbθ]
    have hterm : ∀ k, (P z k).re * l (Pi.single k 1) + (P z k).im * l (Pi.single k Complex.I) =
        -(4 * Real.pi) * (P z k * B k).re := by
      intro k
      have hπ := Real.pi_ne_zero
      simp only [B, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    have h1 : l (P z) = ∑ i, ∑ j, ∑ τ, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [linear_expand l (P z), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => hterm _
    have h2 : -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re =
        ∑ τ, ∑ i, ∑ j, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      simp only [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hr : l (P z) = -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [h1, h2]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    rw [hr]
    push_cast
    ring
  simp only [Function.comp_apply, hpt]
  exact key
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_uniqueness_realComponents_adelicHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  atlas_forward_decl GlobalTheory.FourierRealPart.integral_preimage_eq_zero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicStripSet_measurable_read_on_realPart : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W (Rgrp W (rat x₀)) C) ∧ ∃ S : Set (Mx D W.rank ρ), MeasurableSet S ∧ (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) ∧ ∀ (h : GA D W) (u : UX D ρ), mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) ∈ S ↔ h ∈ strip W (Rgrp W (rat x₀)) C := by
  first | exact @GlobalTheory.StripBorel.strip_measurable | exact GlobalTheory.StripBorel.strip_measurable | (intros; apply GlobalTheory.StripBorel.strip_measurable <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.QuotUnfBound

variable {D : D7}

theorem unitaryAdelicHeight_wittEmbedding_le {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : GA D V₀, height V (d.emb0 g) ≤ C * height V₀ g := by
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F d.j0 d.p0 (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
  refine ⟨max (C : ℝ) 1, le_max_right _ _, fun g => ?_⟩
  have h := hC (Formalism.L2.Theta.matHom V (d.emb0 g)) (Formalism.L2.Theta.matHom V₀ g) (by
      show Formalism.L2.Theta.mt V (d.emb0 g) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel) (by
      rw [← map_inv, ← map_inv, ← map_inv]
      show Formalism.L2.Theta.mt V (d.emb0 g⁻¹) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g⁻¹ ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel)
  have h' : height V (d.emb0 g) ≤ (C : ℝ) * height V₀ g := by
    unfold GlobalTheory.Grow.height; exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (height_pos V₀ g).le)

theorem covolOne_lintegral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' ⬝ M = 1) (hMM' : M ⬝ M' = 1)
    (hM : M ∈ ratMx D n n) (hM' : M' ∈ ratMx D n n) (φ : Mx D m n → ℝ≥0∞)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a ⬝ M
      invFun := fun a => a ⬝ M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x ⬝ M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  have hmeq : Measure.map e μ = μ := GlobalTheory.MixModel.covolOne_measure_eq hμ h1
  haveI := hμ.1
  have h1' := h1
  rw [hmeq] at h1'
  have hfd : ∫⁻ a in e '' 𝓕, φ a ∂μ = ∫⁻ a in 𝓕, φ a ∂μ :=
    h1'.2.1.setLIntegral_eq hμ.2.1 φ fun γ a => hφ γ γ.2 a
  have hmap : ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) = ∫⁻ a in 𝓕, φ (e a) ∂μ := by
    rw [hemb.restrict_map, hemb.lintegral_map, Set.preimage_image_eq _ e.injective]
  calc ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ (e a) ∂μ := rfl
    _ = ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) := hmap.symm
    _ = ∫⁻ a in e '' 𝓕, φ a ∂μ := by rw [hmeq]
    _ = ∫⁻ a in 𝓕, φ a ∂μ := hfd

theorem enorm_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V₀ W : HSp D} {ρ : ℕ}
    {F : WO V₀ W → ℂ} (hF : IsThetaFunO ψ V₀ W F) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    ∀ β ∈ ratMx D ρ V₀.rank, ∀ b, ‖F (rat x₀ ⬝ (β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ := by
  rintro _ ⟨β, rfl⟩ b
  show ‖F (rat x₀ ⬝ (rat β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ
  have e1 : rat x₀ ⬝ (rat β + b) = Formalism.L2.Theta.ratW W V₀ (x₀ ⬝ β) + rat x₀ ⬝ b := by
    rw [Matrix.mul_add]
    congr 1
    show (x₀.map (incA D)) ⬝ (β.map (incA D)) = (x₀ ⬝ β).map (incA D)
    rw [Matrix.map_mul]
  rw [e1, hF.quasi, enorm_mul, GlobalTheory.Unf.FlatForm.enorm_psi hψ, one_mul]

theorem inner_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) {γ : GA D V₀}
    (hγ : γ ∈ GQ V₀) (x : Mx D W.rank ρ) :
    ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x (rat x₀ ⬝ b)‖ₑ ∂vb.μ =
      ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 Ψ x (rat x₀ ⬝ b)‖ₑ ∂vb.μ := by
  set F := d.mixS W ψ vS.μ vS.𝓕 Ψ x with hFdef
  have hF : IsThetaFunO ψ V₀ W F := GlobalTheory.MixValues.mixS_theta D ψ hW.std V V₀ W ρ d vS.μ vS.𝓕 vS.covol Ψ hΨ x
  have hcore := (GlobalTheory.MixSourceFormulas.mixed_source D ψ V V₀ W ρ d χV χW om om' hW hW' vS.μ vS.𝓕 vS.covol Ψ hΨ).core γ x
  have hsub : ∀ w, d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x w = F (w ⬝ Formalism.L2.Theta.mt V₀ γ) := by
    intro w
    rw [hcore]
    have h := GlobalTheory.Unf.om_rat_mul D ψ V₀ W χV χW om' hW' F hF γ hγ 1 (one_mem _) 1 1 w
    rw [mul_one, mul_one, inv_one, show ((1 : GA D V₀), (1 : GA D W)) = 1 from rfl, map_one] at h
    rw [h]
    simp [Formalism.L2.Theta.mt]
  have hM := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ).1 hγ
  have hM' := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ⁻¹).1 (inv_mem hγ)
  have h1 : Formalism.L2.Theta.mt V₀ γ⁻¹ ⬝ Formalism.L2.Theta.mt V₀ γ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.inv_mul _
  have h2 : Formalism.L2.Theta.mt V₀ γ ⬝ Formalism.L2.Theta.mt V₀ γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.mul_inv _
  have hmul : ∀ b : Mx D ρ V₀.rank, rat x₀ ⬝ b ⬝ Formalism.L2.Theta.mt V₀ γ = rat x₀ ⬝ (b ⬝ Formalism.L2.Theta.mt V₀ γ) :=
    fun b => Matrix.mul_assoc _ _ _
  simp_rw [hsub, hmul]
  exact covolOne_lintegral_mul_right vb.covol (Formalism.L2.Theta.mt V₀ γ) (Formalism.L2.Theta.mt V₀ γ⁻¹) h1 h2 hM hM'
    (fun b => ‖F (rat x₀ ⬝ b)‖ₑ) (enorm_periodic hW.std hF x₀)

theorem unfolded_rat_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ)
    (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) {Φ : WO V W → ℂ}
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W)) {γ : GA D V₀} (hγ : γ ∈ GQ V₀) (g : GA D V₀) :
    ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 (γ * g), h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ =
      ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ := by
  refine lintegral_congr fun h => ?_
  congr 1
  refine lintegral_congr fun u => ?_
  have e : om (d.emb0 (γ * g), h) Φ = om (d.emb0 γ, 1) (om (d.emb0 g, h) Φ) := by
    rw [map_mul, show ((d.emb0 γ * d.emb0 g, h) : GA D V × GA D W) = (d.emb0 γ, 1) * (d.emb0 g, h) by
      simp [Prod.mk_mul_mk], map_mul]
    rfl
  rw [e]
  exact inner_inv d hW hW' vS vb x₀ (hW.om_pres _ Φ hΦ) hγ _

end GlobalTheory.QuotUnfBound

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om hW vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hW'⟩ :=
    ((GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)) ψ V W χV χW om hW).1 V₀ ρ d
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.UnfoldBound.unfolded_integral_le D ψ V V₀ W ρ d χV χW om om' hW hW' vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨C₁, hC₁1, hC₁⟩ := GlobalTheory.QuotUnfBound.unitaryAdelicHeight_wittEmbedding_le d
  have hM : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
  have hKpos : (0 : ℝ) < max C 1 * C₁ ^ A := mul_pos hM (pow_pos (one_pos.trans_le hC₁1) A)
  refine ⟨max C 1 * C₁ ^ A, A, fun g => ?_⟩
  have hb : ∀ k : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 k, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ k ^ A) := by
    intro k
    rw [← ENNReal.ofReal_mul hKpos.le]
    refine (hC (d.emb0 k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ height V (d.emb0 k) := (height_pos V _).le
    have h1 : height V (d.emb0 k) ^ A ≤ (C₁ * height V₀ k) ^ A := pow_le_pow_left₀ h0 (hC₁ k) A
    calc C * height V (d.emb0 k) ^ A ≤ max C 1 * height V (d.emb0 k) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 A)
      _ ≤ max C 1 * (C₁ * height V₀ k) ^ A := mul_le_mul_of_nonneg_left h1 hM.le
      _ = max C 1 * C₁ ^ A * height V₀ k ^ A := by rw [mul_pow, mul_assoc]
  have hle : ∀ γ : GQ V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ ((γ : GA D V₀) * g) ^ A) := by
    intro γ
    rw [← GlobalTheory.QuotUnfBound.unfolded_rat_inv d hW hW' vS vb vU vW x₀ G hΦ 𝓑 γ.2 g]
    exact hb _
  rw [ENNReal.ofReal_mul hKpos.le, GlobalTheory.MixSumBound.ofReal_quotHeight_pow,
    ENNReal.mul_iInf_of_ne (by simpa using hKpos) ENNReal.ofReal_ne_top]
  exact le_iInf hle

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  atlas_forward_decl GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 400000 in

theorem tot_continuous (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) : Continuous (a.tot G Φ) := by
  obtain ⟨vT⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 0 V₀.rank
  have hmix := (GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W ρ 0 a.d (hypZero W) a.vS vT a.χV a.χW a.om
    ha.weil Φ hΦ).1
  have hpos : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      (⟨a.d.nB p.2.2 * a.d.levi p.2.1.1, mul_mem (a.d.nB_mem_NFlag _) (a.d.levi_mem_NFlag p.2.1.2)⟩ : flagN a.d) :=
    ((a.d.continuous_nB.comp continuous_snd.snd).mul
      ((a.d.continuous_levi.comp continuous_subtype_val).comp continuous_snd.fst)).subtype_mk _
  have hTh : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.Th p.1.2 (a.d.nB p.2.2 * a.d.levi p.2.1.1) :=
    ha.cont.comp (continuous_fst.snd.prodMk hpos)
  have hM : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2) :=
by
    have h1 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.emb0 (a.g p.1.2) :=
      a.d.continuous_embed.comp (ha.g.comp continuous_fst.snd)
    have h2 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1 : Mx D W.rank ρ) :=
      continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd.fst))
    have h3 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2 : WO V₀ W) :=
      continuous_const.matrix_mul continuous_snd.snd
    have hq : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        (((a.d.emb0 (a.g p.1.2), p.1.1), ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1, (rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      (h1.prodMk continuous_fst.fst).prodMk (h2.prodMk h3)
    have hc := hmix.comp hq
    exact hc
  have hfin := (hG.2.1.comp continuous_fst.fst).mul (hTh.mul hM)
  exact hfin

theorem inner_unfold (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) (y : Y) :
    IntegrableOn (fun h => G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ)) 𝓑
      a.vW.μ ∧
    ∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν =
      ∫ h in 𝓑, G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ := by
  have hD : Descent D := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om', hom'⟩ := (hD ψ V W a.χV a.χW a.om ha.weil).1 V₀ ρ a.d
  have hΦ' := ha.weil.om_pres (a.d.emb0 (a.g y), 1) Φ hΦ
  obtain ⟨h1, h2⟩ := GlobalTheory.Unf.unfold_over_N_lift D hD ψ V V₀ W ρ a.d a.χV a.χW a.om om' ha.weil hom' a.vS a.vN a.vb
    a.vU a.vW a.x₀ (a.Th y) ha.base (ha.th y) G (a.om (a.d.emb0 (a.g y), 1) Φ) hG hΦ' 𝓑 h𝓑
  have hsplit : ∀ h, a.om (1, h) (a.om (a.d.emb0 (a.g y), 1) Φ) = a.om (a.d.emb0 (a.g y), h) Φ := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hlift : ∀ n, liftS a.om a.vW.μ a.vW.𝓕 G (a.om (a.d.emb0 (a.g y), 1) Φ) n =
      liftS a.om a.vW.μ a.vW.𝓕 G Φ (n * a.d.emb0 (a.g y)) := by
    intro n
    have ht := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D ψ V W a.χV a.χW a.om ha.weil a.vW G Φ hG hΦ).2.2.2.2
      (a.d.emb0 (a.g y)) 1
    have hr : rTrans (1 : GA D W) G = G := by funext x; simp [rTrans]
    rw [hr] at ht
    rw [ht]; rfl
  simp only [hsplit, hlift] at h1 h2
  exact ⟨h1, h2⟩

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 1000000 in

theorem tot_integrable [SecondCountableTopology Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y) (ha : a.Is)
    (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G) (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) :
    Integrable (a.tot G Φ) (a.totMeas 𝓑) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D ρ V₀.rank
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight D ψ V V₀ W ρ a.d a.χV a.χW a.om ha.weil a.vS a.vb a.vU a.vW a.x₀ ha.base G Φ
    hG hΦ 𝓑 h𝓑
  obtain ⟨M, -, hMb, hMi⟩ := ha.small
  have hM0 : ∀ y, 0 ≤ M y := fun y => (norm_nonneg _).trans (hMb y 1 (one_mem _))
  set Bd : GA D V₀ → GA D W → ENNReal := fun g h => ∫⁻ u, ∫⁻ b in a.vb.𝓕,
    ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 g, h) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
      ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂a.vb.μ ∂a.vU.ν with hBd
  set F : GA D W × Y → ENNReal := fun q => ENNReal.ofReal (M q.2) * (‖G q.1‖ₑ * Bd (a.g q.2) q.1) with hF
  haveI : SecondCountableTopology (GA D W × Y) := inferInstance
  haveI : OpensMeasurableSpace (GA D W × Y) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (UX D ρ) (Mx D ρ V₀.rank) := secondCountableTopologyEither_of_right _ _
  haveI : OpensMeasurableSpace (UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D W × Y) (UX D ρ × Mx D ρ V₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  have hmeas : Measurable (a.tot G Φ) := (tot_continuous a ha G Φ hG hΦ).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) < ⊤
  have hpt : ∀ q : GA D W × Y, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ≤ F q := by
    intro q
    have hc : ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
    calc ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))
        ≤ ∫⁻ u, ∫⁻ b, ‖a.tot G Φ (q, (u, b))‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := lintegral_prod_le _
      _ ≤ ∫⁻ u, ∫⁻ b, ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ *
            ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := by
          refine lintegral_mono fun u => lintegral_mono fun b => ?_
          have hmem : a.d.nB b * a.d.levi u.1 ∈ flagN a.d := mul_mem (a.d.nB_mem_NFlag b) (a.d.levi_mem_NFlag u.2)
          have hth : ‖a.Th q.2 (a.d.nB b * a.d.levi u.1)‖ₑ ≤ ENNReal.ofReal (M q.2) := by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hMb _ _ hmem)
          show ‖G q.1 * (a.Th q.2 (a.d.nB b * a.d.levi u.1) * a.d.mixS W ψ a.vS.μ a.vS.𝓕
            (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b))‖ₑ ≤ _
          rw [enorm_mul, enorm_mul, ← mul_assoc, mul_comm (‖G q.1‖ₑ), mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ * Bd (a.g q.2) q.1 := by
          simp only [hBd]
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun u => ?_
          rw [← lintegral_const_mul' _ _ hc]
      _ = F q := by simp only [hF, mul_assoc]
  calc ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)))
      ≤ ∫⁻ q, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ∂((a.vW.μ.restrict 𝓑).prod a.m) :=
        lintegral_prod_le _
    _ ≤ ∫⁻ q, F q ∂((a.vW.μ.restrict 𝓑).prod a.m) := lintegral_mono hpt
    _ = ∫⁻ z, F z.swap ∂(a.m.prod (a.vW.μ.restrict 𝓑)) := (lintegral_prod_swap F).symm
    _ ≤ ∫⁻ y, ∫⁻ h, F (h, y) ∂(a.vW.μ.restrict 𝓑) ∂a.m := lintegral_prod_le _
    _ = ∫⁻ y, ENNReal.ofReal (M y) * ∫⁻ h in 𝓑, ‖G h‖ₑ * Bd (a.g y) h ∂a.vW.μ ∂a.m := by
        simp only [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (M y) * ENNReal.ofReal (C * quotHeight V₀ (a.g y) ^ A) ∂a.m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact hCA (a.g y)
    _ = ∫⁻ y, ENNReal.ofReal (C * (M y * quotHeight V₀ (a.g y) ^ A)) ∂a.m := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.ofReal_mul (hM0 y)]
        ring_nf
    _ < ⊤ := ((hMi A).const_mul C).lintegral_lt_top

theorem fubini_tot (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (B₀ : Set (GA D W))
    (hI : Integrable (a.tot G Φ) (a.totMeas B₀)) :
    IntegrableOn (a.ker G Φ) B₀ a.vW.μ ∧ ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ h in B₀, a.ker G Φ h ∂a.vW.μ ∧
    ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ y, ∫ h in B₀,
      G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ ∂a.m := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI' : Integrable (a.tot G Φ) (((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) :=
    hI
  set K : GA D W × Y → ℂ := fun q =>
    G q.1 * fl ψ a.d W a.vS a.vb a.vU (a.Th q.2) (rat a.x₀) (a.om (a.d.emb0 (a.g q.2), q.1) Φ) with hK
  have hae : (fun q => ∫ r, a.tot G Φ (q, r) ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) =ᵐ[(a.vW.μ.restrict B₀).prod a.m]
      K := by
    filter_upwards [hI'.prod_right_ae] with q hq
    rw [integral_prod _ hq]
    simp only [Gen.tot, integral_const_mul, hK, fl]
  have hKi : Integrable K ((a.vW.μ.restrict B₀).prod a.m) := hI'.integral_prod_left.congr hae
  have hker : ∀ h, ∫ y, K (h, y) ∂a.m = a.ker G Φ h := by
    intro h
    simp only [hK, Gen.ker, integral_const_mul]
  have htot : ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ q, K q ∂((a.vW.μ.restrict B₀).prod a.m) := by
    show ∫ p, a.tot G Φ p ∂(((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) = _
    rw [integral_prod _ hI']
    exact integral_congr_ae hae
  refine ⟨?_, ?_, ?_⟩
  · have := hKi.integral_prod_left
    simp only [hker] at this
    exact this
  · rw [htot, integral_prod _ hKi]
    simp only [hker]
  · rw [htot, integral_prod_symm _ hKi]

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc

set_option maxHeartbeats 1000000 in

theorem unfold_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI := Gen.tot_integrable a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨hker, -, hE⟩ := Gen.fubini_tot a ha G Φ 𝓑 hI
  refine ⟨hI, hker, ?_, ?_⟩
  · rw [hE, Gen.lhs]
    exact integral_congr_ae (ae_of_all _ fun y => (Gen.inner_unfold a ha G Φ hG hΦ 𝓑 h𝓑 y).2)
  · intro S hS
    have hset : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        (S ×ˢ (Set.univ : Set Y)) ×ˢ (Set.univ : Set (UX D ρ × Mx D ρ V₀.rank)) := by
      ext p; simp
    have hres : (a.totMeas 𝓑).restrict {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        a.totMeas (𝓑 ∩ S) := by
      simp only [Gen.totMeas]
      rw [hset, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ,
        Measure.restrict_restrict hS, Set.inter_comm]
    have hI' : Integrable (a.tot G Φ) (a.totMeas (𝓑 ∩ S)) := by
      rw [← hres]; exact hI.restrict
    rw [hres]
    exact ((Gen.fubini_tot a ha G Φ (𝓑 ∩ S) hI').2.1).symm

end GlobalTheory.Asc

example : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) :=
  GlobalTheory.Asc.unfold_family
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_unfolding_integrated_over_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  atlas_forward_decl GlobalTheory.Asc.unfold_family
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.StripVanish

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]

theorem dualPair_action_embedded_hyperbolic_extY (d : HypDec V V₀ ρ) (g : GA D V₀) (h : GA D W) (c : Mx D W.rank ρ) :
    actO V W (d.emb0 g) h (d.extY W c) = d.extY W (Formalism.L2.Theta.mt W h ⬝ c) := by
  simp only [actO]
  rw [show (d.emb0 g)⁻¹ = d.emb0 g⁻¹ from (map_inv _ _).symm]
  simp only [ HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc, HypDec.wittDecomp_projY_anisotropicEmbedding]

theorem symplO_extX_extY_mt (d : HypDec V V₀ ρ) (h : GA D W) (x c : Mx D W.rank ρ) :
    symplO V W (d.extX W x) (d.extY W (Formalism.L2.Theta.mt W h ⬝ c)) =
      symplO V W (d.extX W (Formalism.L2.Theta.mt W h⁻¹ ⬝ x)) (d.extY W c) := by
  rw [← GlobalTheory.SplitHecke.symplO_actO V W 1 h⁻¹]
  congr 1
  · simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]
  · simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem tot_heisO_extY (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ)
    (c : Mx D W.rank ρ) (p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) :
    a.tot G (heisO ψ V W (a.d.extY W c) Φ) p =
      ψ (symplO V W (a.d.extX W (Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1))) (a.d.extY W c)) *
        a.tot G Φ p := by
  simp only [Gen.tot, flFun]
  rw [ha.weil.om_heis _ _ _ _ hΦ, dualPair_action_embedded_hyperbolic_extY,
    (@GlobalTheory.HeisMixSource.heis_mixS D ψ ha.weil.std V V₀ W ρ a.d a.vS _ (ha.weil.om_pres _ _ hΦ)).2.1, Pi.smul_apply, smul_eq_mul,
    symplO_extX_extY_mt]
  ring

def pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (q : GA D W × UX D ρ) : Mx D W.rank ρ :=
  Formalism.L2.Theta.mt W q.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ q.2.1.1)

theorem measurable_pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Measurable (pointHU (W := W) x₀) := by
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  haveI : SecondCountableTopologyEither (GA D W) (UX D ρ) := secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace (GA D W × UX D ρ) := Prod.opensMeasurableSpace
  exact (((continuous_mt W).comp continuous_fst.inv).matrix_mul
      (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))).measurable

theorem measurable_point (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1) := by
  have h1 : Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable (pointHU (W := W) x₀ ∘ fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1)) :=
    Measurable.comp (measurable_pointHU x₀) h1
  exact h2

end GlobalTheory.StripVanish

open GlobalTheory.StripVanish in

theorem GlobalTheory.StripVanish.integral_strip_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ), RapidDec W G → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → a.lhs G (heisO ψ V W (a.d.extY W c) Φ) = 0) → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → ∫ h in 𝓑 ∩ strip W (Rgrp W (rat a.x₀)) C, a.ker G Φ h ∂a.vW.μ = 0 := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G hG Φ hΦ hvan 𝓑 h𝓑 C hC hCinf
  obtain ⟨hSmeas, S, hS, hSinf, hSiff⟩ := GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D W ρ a.x₀ ha.base C hC hCinf
  obtain ⟨hint, -, -, hres⟩ := GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ V V₀ W ρ Y a ha G Φ hG hΦ 𝓑 h𝓑
  rw [hres _ hSmeas]
  have hpre : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ strip W (Rgrp W (rat a.x₀)) C} =
      (fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)) ⁻¹' S := by
    ext p
    exact (hSiff p.1.1 p.2.1).symm
  rw [hpre]
  refine GlobalTheory.T.fourier_uniqueness_realComponents_adelicHom D ψ ha.weil.std V V₀ W ρ a.d _ (a.totMeas 𝓑) (a.tot G Φ) hint _ (measurable_point a.x₀) ?_ S hS hSinf
  intro c hc
  have h0 := hvan c hc
  rw [(GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ V V₀ W ρ Y a ha G _ hG (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all ha.weil.std hΦ _) 𝓑 h𝓑).2.2.1] at h0
  simpa only [tot_heisO_extY a ha G Φ hΦ c] using h0
end
end
