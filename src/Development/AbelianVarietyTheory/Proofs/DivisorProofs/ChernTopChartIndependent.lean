import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] {X : Var F} {ι : Type} [Finite ι]

def ofDivisors (Δ : ι → X.Dv) : Fr (ratOf X) (fun _ : ι => 1) 0 where
  S z := {A | ∀ i, (Δ i).GeneratesAt z (A i 0 0)}
  loc z := by
    have := Fintype.ofFinite ι
    choose U hz g hg using fun i => (Δ i).exists_isEqn_nhds z
    let W : X.X.Opens := ⨅ i, U i
    have hW : z ∈ W := by
      show z ∈ ((⨅ i, U i : X.X.Opens) : Set X.X)
      rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.2 hz
    refine ⟨W, fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹, hW, fun _ => by simp, fun z' hz' A => ?_⟩
    have hz'' (i : ι) : z' ∈ U i := by
      have : z' ∈ ((⨅ i, U i : X.X.Opens) : Set X.X) := hz'
      rw [TopologicalSpace.Opens.coe_iInf] at this; exact Set.mem_iInter.1 this i
    have e (i : ι) (a b : Fin 1) : (A * (fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹ :
        Mat (fun _ : ι => 1) X.Fn)⁻¹) i a b = A i 0 0 * g i := by
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.mul_apply, Matrix.inv_def]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have h' := ((hg i z' (hz'' i)).generatesAt_iff).1 (h i)
      refine ⟨fun a b => ?_, ?_, ?_, fun a b ha => absurd ha (by simp)⟩
      · rw [e]; exact mem_O_ratOf.2 h'.regAt
      · rw [Matrix.det_unique, e]; exact h'.ne_zero
      · rw [Matrix.det_unique, e]; exact mem_O_ratOf.2 h'.inv.regAt
    · obtain ⟨h1, h2, h3, -⟩ := h i
      rw [Matrix.det_unique, e] at h2 h3
      exact ((hg i z' (hz'' i)).generatesAt_iff).2
        ((unitAt_iff h2).2 ⟨mem_O_ratOf.1 (e i 0 0 ▸ h1 0 0), mem_O_ratOf.1 h3⟩)

theorem isGraded_ofDivisors (Δ : ι → X.Dv) : IsGraded (lineFlag (ofDivisors Δ)) fun x => Δ x.1 := by
  refine ⟨1, fun i => ⟨1, (Δ i).isEqn_genericPoint 1, by simpa using unitAt_one _⟩, fun y x => ?_⟩
  choose g hg using fun i => (Δ i).exists_isEqn y
  refine ⟨fun i => Matrix.diagonal fun _ => (g i : X.Fn)⁻¹,
    fun i => CartierDiv.isEqn_iff_generatesAt_inv.1 (hg i), g x.1, ?_, hg x.1⟩
  obtain ⟨i, a⟩ := x
  rw [Subsingleton.elim a 0]
  simp [Matrix.inv_def]

end GlobalTheory.ChernWeilLine

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] [NumberField F] {ι : Type}

def lineGram {Y : Var F} {σ : F →+* ℂ} {Δ : ι → Y.Dv} (C : CxSt F) (m : ∀ i, C.Met Y σ (Δ i)) :
    Mat (fun _ : ι => 1) Y.Fn → Pts Y σ → Mat (fun _ : ι => 1) ℂ :=
  fun A y i => Matrix.of fun _ _ => ((C.pn Y σ (Δ i) (m i) (C.cx Y σ (A i 0 0)) y : ℝ) : ℂ)

end GlobalTheory.ChernWeilLine
end
end

section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine

theorem GlobalTheory.ChernWeilLine.chernTop_lineGram_trans : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i, (cxSt F).Met Y σ (Δ i)), IsMetricOn (ofDivisors Δ) ⊤ (lineGram (cxSt F) m) → ∀ (t : ι → ℝ) (c c' : GlobalTheory.AlgChart Y.str σ Y.dim) (y : Pts Y σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ A ∈ (ofDivisors Δ).S (under y), chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c'.e.symm v)) (c'.e y) := by
  intro F _ _ Y σ ι _ Δ m hM t c c' y hy hy' A hA
  set R : MvPolynomial (ι × ℕ) ℝ := (∑ i, C (t i) * X (i, 1)) ^ Y.dim
  let K : V Y.dim → Mat (fun _ : ι => 1) ℂ := fun v => lineGram (cxSt F) m A (c'.e.symm v)
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have hφ : AnalyticAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo_trans c') (ho.mem_nhds hm)
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hy'' : c'.e.symm (c'.e y) = y := c'.e.left_inv hy'
  have hsm := hM.smooth y mem_ptsIn_top A hA
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (c'.e y) := by
    intro τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).2
    have hn : ∀ {f : Pts Y σ → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt f z) → ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y) := by
      intro f hf
      have hs : c'.e.target ∩ c'.e.symm ⁻¹' {z | CInfAt f z} ∈ 𝓝 (c'.e y) := by
        refine Filter.inter_mem (c'.e.open_target.mem_nhds (c'.e.map_source hy')) ?_
        exact (c'.e.continuousAt_symm (c'.e.map_source hy')).preimage_mem_nhds (hy''.symm ▸ hf)
      exact ((contDiffOn_chart (fun z hz => hz) c').contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (c'.e y) τ).det := by
    intro τ
    have hp := hM.posDef y mem_ptsIn_top A hA τ
    simp only [K, hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp R K (c'.e ∘ c.e.symm) (c.e y) hφ (e₂ ▸ hK2) (e₂ ▸ hKu)
  have hg : (fun v => lineGram (cxSt F) m A (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun w => K ((c'.e ∘ c.e.symm) w) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [K, Function.comp_apply, c'.e.left_inv hw.2]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr R hg, key, e₂, transDet, Complex.sq_norm]
end
end
