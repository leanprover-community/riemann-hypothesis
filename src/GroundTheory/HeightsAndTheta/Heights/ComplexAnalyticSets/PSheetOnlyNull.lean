module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetOnlyNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace SheetOnlyNull

variable {n d : ℕ}

theorem injective_iff_det_ne_zero (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem differentiableOn_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U :=
  (LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs

theorem analyticOnNhd_of_differentiableOn {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := fun w hw =>
  AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU
    (differentiableOn_pi.1 hF i) w hw

theorem analyticOnNhd_det_jacC {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero_of {J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A' : Matrix (Fin d) (Fin n) ℂ} {D : Set (Fin d → ℂ)} (hD : IsOpen D) {y₀ : Fin d → ℂ}
    (hy₀ : y₀ ∈ D) {f : (Fin d → ℂ) → Fin n → ℂ} (hf : DifferentiableOn ℂ f D) {x' : Fin n → ℂ}
    (hfx : f y₀ = x') (hmem : ∀ w ∈ D, f w ∈ zeroSet J')
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ f w) y₀).det ≠ 0)
    (hloc : ∀ S : Set (Fin d → ℂ), IsOpen S → y₀ ∈ S → S ⊆ D →
      ∃ N ∈ 𝓝 x', ∀ x'' ∈ zeroSet J' ∩ N, ∃ w ∈ S, x'' = f w) :
    ∃ s', IsSheetAt J' A' x' s' := by
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ f w with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_mulVec A' hf
  have hFa := analyticOnNhd_of_differentiableOn hD hFd
  set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (analyticOnNhd_det_jacC hD hFd).continuousOn
    |>.isOpen_inter_preimage hD isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hy₀, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : y₀ ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F y₀ = A' *ᵥ x' := by simp only [hFdef, hfx]
  have hsym : φ.symm (A' *ᵥ x') = y₀ := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  obtain ⟨N, hN, hNloc⟩ := hloc (φ.source ∩ D) (φ.open_source.inter hD) ⟨hysrc, hy₀⟩ Set.inter_subset_right
  refine ⟨f ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hy₀, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hfx], fun z hz => ⟨?_, hmem _ hz.2.1⟩, N, hN, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hf.differentiableAt (hD.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · rintro x'' hx'' -
    obtain ⟨w, hw, hx''w⟩ := hNloc x'' hx''
    have hA' : A' *ᵥ x'' = φ w := by rw [hφ, hFdef, hx''w]
    rw [Function.comp_apply, hA', φ.left_inv hw.1, hx''w]

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  refine exists_sheet_of_det_ne_zero_of hU hyU hsd hsx (fun w hw => (hsec w hw).2) hdet fun S hS hyS hSU => ?_
  refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' S,
    inter_mem hV ((hS.preimage (by fun_prop)).mem_nhds hyS), ?_⟩
  rintro x'' ⟨hx''Z, hx''V, hx''S⟩
  exact ⟨A *ᵥ x'', hx''S, hVs x'' ⟨hx''Z, hx''V⟩ (hSU hx''S)⟩

theorem exists_det_ne_zero_of (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A' : Matrix (Fin d) (Fin n) ℂ} (hJ' : J'.IsPrime) (hA' : IsFiniteProjection J' A')
    {D : Set (Fin d → ℂ)} (hD : IsOpen D) {f : (Fin d → ℂ) → Fin n → ℂ} (hf : DifferentiableOn ℂ f D)
    {W₀ : Set (Fin d → ℂ)} {x' : Fin n → ℂ} (hx' : x' ∈ zeroSet J') {N : Set (Fin n → ℂ)} (hN : N ∈ 𝓝 x')
    (hsub : ∀ z ∈ zeroSet J' ∩ N, ∃ w ∈ W₀ ∩ D, f w = z) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ f w) w).det ≠ 0 := by
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ f w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ D) ⊆ F '' {w | w ∈ D ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d D F hD (differentiableOn_mulVec A' hf))
  have hnhds := h₁ n d J' (linPoly A') hJ' hA'.injective hA'.finite x' hx' N hN
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub' : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J' ∩ N) ⊆
      F '' (W₀ ∩ D) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hfw⟩ := hsub z hz
    exact ⟨w, hw, by simp only [hFdef, hfw]⟩
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub')
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  refine exists_det_ne_zero_of h₁ h₂ hJ hA' hU hsd (hsx ▸ (hsec _ hyU).2)
    (inter_mem hV (((hW₀.inter hU).preimage (by fun_prop)).mem_nhds ⟨hxW₀, hyU⟩)) ?_
  rintro z ⟨hzZ, hzV, hzW⟩
  exact ⟨A *ᵥ z, hzW, (hVs z ⟨hzZ, hzV⟩ hzW.2).symm⟩

end SheetOnlyNull

theorem SheetOnlyNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : SheetOnlyNull.Statement := by
  intro n d J A A' hJ _ _ hA'
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hAx
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono hball,
      SheetOnlyNull.exists_det_ne_zero h₁ h₂ hJ hA' hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end GroundTheory.Heights₂.Heights
