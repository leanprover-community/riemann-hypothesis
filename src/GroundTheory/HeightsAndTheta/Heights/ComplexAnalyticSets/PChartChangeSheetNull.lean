module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartChangeSheetNull

variable {n d : ℕ}

theorem eval_linForm (u x : Fin n → ℂ) : eval x (linForm u) = linEval u x := by
  simp [linForm, linEval]

theorem continuous_linEval (u : Fin n → ℂ) : Continuous (linEval u) := by
  unfold linEval
  fun_prop

theorem exists_poly_of_linForm {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) c = 0 := by
  classical
  have hv0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hu
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J (linForm u)) = 0 := by
    obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hdeg : (Polynomial.X * q).natDegree = q.natDegree + 1 :=
      Polynomial.natDegree_X_mul hqm.ne_zero
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero] at hp
    refine Nat.find_min hex (m := q.natDegree) (by omega) ⟨q, hqm, rfl, ?_⟩
    exact hp.resolve_left hv0
  have hQ : Ideal.Quotient.mk J (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := by
    rw [Polynomial.hom_eval₂]; exact hp
  have hQJ := Ideal.Quotient.eq_zero_iff_mem.1 hQ
  refine ⟨p.coeff 0, hc0, fun x hx hux => ?_⟩
  have h1 : eval x (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := hx _ hQJ
  rw [Polynomial.hom_eval₂, eval_linForm, hux, Polynomial.eval₂_at_zero] at h1
  have h2 : eval x (pullback A (p.coeff 0)) = 0 := h1
  rwa [ComplexSets.eval_pullback] at h2

theorem volume_image_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    volume ((fun x => A *ᵥ x) '' {x | x ∈ zeroSet J ∧ linEval u x = 0}) = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_poly_of_linForm hJ hA hu
  refine measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)
  rintro _ ⟨x, ⟨hx, hux⟩, rfl⟩
  exact hcz x hx hux

theorem isOpen_dom {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    (u : Fin n → ℂ) (hUs : IsOpen Us) (hsd : DifferentiableOn ℂ s Us) (hU : IsOpen U) :
    IsOpen (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  hsd.continuousOn.isOpen_inter_preimage hUs
    (hU.inter (isOpen_ne_fun (continuous_linEval u) continuous_const))

theorem differentiableOn_tau {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    {Ψ : (Fin n → ℂ) → Fin n → ℂ} (u : Fin n → ℂ) (A' : Matrix (Fin d) (Fin n) ℂ)
    (hsd : DifferentiableOn ℂ s Us) (hΨ : DifferentiableOn ℂ Ψ U) :
    DifferentiableOn ℂ (fun w => A' *ᵥ Ψ (s w)) (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  SheetOnlyNull.differentiableOn_mulVec A' (s := Ψ ∘ s)
    (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1)

theorem exists_sheet_of_det_ne_zero {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J' A' (Ψ x) s' := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  refine SheetOnlyNull.exists_sheet_of_det_ne_zero_of (isOpen_dom u hUs hsd hU)
    ⟨hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩
    (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1) (congrArg Ψ hsx)
    (fun w hw => (hΨm ⟨(hsec _ hw.1).2, hw.2.2⟩).1) hdet fun S hS hyS hSD => ?_
  have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' S ∈ 𝓝 x :=
    inter_mem hV ((hS.preimage (by fun_prop)).mem_nhds hyS)
  refine ⟨{z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' S),
    inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
      (hΦc.preimage_mem_nhds (by rw [hΦΨ x ⟨hxZ, hxu⟩]; exact hnx)), ?_⟩
  rintro x'' ⟨hx''Z, hx''u, hx''V, hx''S⟩
  have hx''P : x'' ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hx''Z, hx''u⟩
  exact ⟨A *ᵥ Φ x'', hx''S, by simp only [Function.comp_apply]; rw [← hVs _ ⟨(hΦm hx''P).1, hx''V⟩ (hSD hx''S).1, hΨΦ x'' hx''P]⟩

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hJ' : J'.IsPrime) (hA' : IsFiniteProjection J' A')
    (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) w).det ≠ 0 := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})
  have hD : IsOpen D := isOpen_dom u hUs hsd hU
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D) ∈ 𝓝 x :=
    inter_mem hV (((hW₀.inter hD).preimage (by fun_prop)).mem_nhds
      ⟨hxW₀, hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩)
  refine SheetOnlyNull.exists_det_ne_zero_of h₁ h₂ hJ' hA' hD
    (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1) hP.1
    (inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
      (hΦc.preimage_mem_nhds (by rw [hΦΨ x ⟨hxZ, hxu⟩]; exact hnx))) ?_
  rintro z ⟨hzZ, hzu, hzV, hzW⟩
  have hzP : z ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hzZ, hzu⟩
  exact ⟨A *ᵥ Φ z, hzW, by simp only [Function.comp_apply]; rw [← hVs (Φ z) ⟨(hΦm hzP).1, hzV⟩ hzW.2.1, hΨΦ z hzP]⟩

end ChartChangeSheetNull


open ChartChangeSheetNull in
theorem ChartChangeSheetNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : ChartChangeSheetNull.Statement := by
  intro n d J J' A A' u u' U U' Φ Ψ hJ _ hJ' _ hu _ hA hA' hU hU' hUsub hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ linEval u x ≠ 0 ∧
    ¬ ∃ s', IsSheetAt J' A' (Ψ x) s'} with hBdef
  choose σ Us W hUs hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    have hxU : x ∈ U := hUsub ⟨hxB.1, hxB.2.2.1⟩
    have hD := isOpen_dom u (hUs i) (hσd i) hU
    have hsx : σ i (A *ᵥ x) = x := by obtain ⟨_, _, _, _, h, _⟩ := hsh; exact h
    have hAxD : A *ᵥ x ∈ Us i ∩ σ i ⁻¹' (U ∩ {x | linEval u x ≠ 0}) :=
      ⟨hAx, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxB.2.2.1⟩⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD _ hAxD
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ Ψ (σ i v)) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD (differentiableOn_tau u A' (hσd i) hΨ)).mono hball,
      exists_det_ne_zero h₁ h₂ hJ' hA' hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hxB.2.2.1 hxU hsh
        Metric.isOpen_ball (Metric.mem_ball_self hr), ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2.2 (exists_sheet_of_det_ne_zero hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hx''B.2.2.1
      (hUsub ⟨hx''B.1, hx''B.2.2.1⟩) (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  have hBnull : volume ((fun x => A *ᵥ x) '' B) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
    rintro _ ⟨x, hxB, rfl⟩
    have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
  refine measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hu))
  rintro _ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩
  by_cases hux : linEval u x = 0
  · exact Or.inr ⟨x, ⟨hxZ, hux⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hxZ, hxs, hux, fun h => hnot ⟨hux, h⟩⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
