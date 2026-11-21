import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
open ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_isCInf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L),
    φ.IsCInf → ψ.IsCInf →
      φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y L φ ψ hφ hψ
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  set v : CxPts Y.str (RingHom.id ℂ) → ℝ :=
    fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 with hv
  have hdiff : ∀ i y, y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (ψ.φ i y - φ.φ i y) / 2 = v y := by
    intro i y hy
    have hp := mem_pick φ.isLB y
    simp only [hv]
    rw [ψ.trans i _ y hy hp, φ.trans i _ y hy hp]
    ring
  have hvC : ∀ y, CInfAt v y := by
    intro y
    have hp := mem_pick φ.isLB y
    refine (((hψ _ y hp).add (hφ _ y hp).neg).const_mul (1 / 2)).congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hp] with z hz
    rw [← hdiff _ z hz]
    ring
  have hvs : (R.finAtlas).Smooth v :=
    (hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hvC y)
  have sφ := (Weight.isCInf_iff_isSmooth R).1 hφ
  have sψ := (Weight.isCInf_iff_isSmooth R).1 hψ
  have hQ : IsPotential R.finAtlas (φ.locPot + LocPot.ofFun v) :=
    isPotentialAdd _ _ _ (Weight.isPotential_locPot sφ) (isPotential_ofFun _ _ hvs)
  have hS : SameForm R.finAtlas ψ.locPot (φ.locPot + LocPot.ofFun v) :=
    ψ.sameForm_of_re (R := R) hA hQ fun x => by
      refine ⟨pick φ.isLB x, mem_pick φ.isLB x, _, isOpen_ptsIn _, mem_pick φ.isLB x, fun _ => 0,
        fun _ => differentiableOn_const (0 : ℂ), fun z hz => ?_⟩
      have := hdiff _ z hz
      show ψ.φ _ z / 2 = (φ.φ _ z / 2 + v z) + _
      rw [← this]
      simp
      ring
  rw [(Weight.chernInt_eq_mInt R hφ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ),
    (Weight.chernInt_eq_mInt R hψ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y ψ hψ),
    SameForm.mInt_eq (fun _ => hS) _]
  exact (massIndep R.finAtlas (fun _ => φ.locPot) (fun _ => v)
    (fun _ => Weight.isPotential_locPot sφ) (fun _ => hvs)).symm

end GlobalTheory.CompanionTheory.ChernMass
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_weight_indep : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_isCInf
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.ChartGlue GlobalTheory.ProjVar.Var

namespace GlobalTheory.CompanionTheory.ChernTransport

section Chart

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B B' : LB X} {φ : Weight p σ B} {ψ : Weight p σ B'}

theorem hess_eq_of_unit (c : AlgChart p σ D) (h : φ.IsCInf) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {i : B.ι} {j : B'.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B'.U j))
    (a : Γ(X, B.U i ⊓ B'.U j)ˣ)
    (ha : ∀ z ∈ ptsIn p σ (B.U i ⊓ B'.U j),
      ψ.φ j z = φ.φ i z + Real.log (‖ev p σ _ a.val z‖ ^ 2)) :
    c.hess ψ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B'.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ a.val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B'.U j),
      (ev p σ _ a.val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 a.isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ a.val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext s t
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 s t
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ha _ hv.2, one_mul]
  rfl

theorem chartMeas_congr_source {n : ℕ} {T : Type} [TopologicalSpace T] [MeasurableSpace T]
    (e : OpenPartialHomeomorph T (V n)) {ρ ρ' : T → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  have hae : (ρ ∘ e.symm) =ᵐ[volume.restrict e.target] (ρ' ∘ e.symm) :=
    (ae_restrict_iff' e.open_target.measurableSet).2
      (Filter.Eventually.of_forall fun v hv => h _ (e.map_target hv))
  show Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) =
    Measure.map e.symm ((volume.restrict e.target).withDensity (ρ' ∘ e.symm))
  rw [withDensity_congr_ae hae]

theorem chernPart_eq_of_chernDens (h : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    c.chernDens ψ y = c.chernDens φ y) (ε : ℤˣ) : ψ.chernPart D ε = φ.chernPart D ε := by
  show (⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens ψ y)) =
    ⨆ c : AlgChart p σ D, chartMeas c.e fun y => ENNReal.ofReal (↑↑ε * c.chernDens φ y)
  exact iSup_congr fun c => chartMeas_congr_source _ fun y hy => by rw [h c y hy]

end Chart

variable {Y : Var ℂ} {Δ : Y.Dv} {L L' : LB Y.X} {r : L.ι → Y.Fnˣ} {r' : L'.ι → Y.Fnˣ}

theorem exists_unit_tv (hp : Presents Δ L r) (hp' : Presents Δ L' r') (i : L.ι) (j : L'.ι) :
    ∃ a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ, ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
      tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z := by
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq (U := L.U i ⊓ L'.U j)
    (f := (r' j : Y.Fn) / (r i : Y.Fn))
    fun x hx => (hp.isEqn i x hx.1).iff_unitAt.1 (hp'.isEqn j x hx.2)
  refine ⟨a, fun z hz => ?_⟩
  have hb := mem_ptsIn_iff.1 hz
  rw [tv, ← ha (gen_mem hb), val_cx_fnOf hb]

theorem exists_transport (hp : Presents Δ L r) (hp' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (hφ : φ.IsCInf) :
    ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
      ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  have hs : mSmooth Y (RingHom.id ℂ) Δ (ofWeight Y (RingHom.id ℂ) Δ L r hp φ) :=
    (mSmooth_ofWeight_iff hp φ).2 ((Weight.isCInf_iff_isSmooth (Y.an _)).1 hφ)
  set m := ofWeight Y (RingHom.id ℂ) Δ L r hp φ with hm
  let ψ : Weight Y.str (RingHom.id ℂ) L' := m.toWeight hs.posSet_eq hp'
  have hψ : ψ.IsCInf := (Weight.isCInf_iff_isSmooth (Y.an _)).2 (hs.isSmooth_toWeight hp')
  have key : ∀ (i : L.ι) (j : L'.ι) (a : Γ(Y.X, L.U i ⊓ L'.U j)ˣ),
      (∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        tv (σ := RingHom.id ℂ) (r i) (r' j) z = ev Y.str (RingHom.id ℂ) _ a.val z) →
      ∀ z ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i ⊓ L'.U j),
        ψ.φ j z = φ.φ i z + Real.log (‖ev Y.str (RingHom.id ℂ) _ a.val z‖ ^ 2) := by
    intro i j a ha z hz
    obtain ⟨hi, hj⟩ := mem_ptsIn_inf.1 hz
    have hw : m.wt (r i) z = φ.φ i z := by
      rw [Met.wt, hm, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
    have := Met.wt_trans (hs.posSet_eq ▸ mem_univ z) (ptsIn_subset_eqnSet hp i hi)
      (ptsIn_subset_eqnSet hp' j hj)
    rw [hw, ha z hz] at this
    exact this
  have hd : ∀ (c : AlgChart Y.str (RingHom.id ℂ) Y.dim), ∀ y ∈ c.e.source,
      c.chernDens ψ y = c.chernDens φ y := by
    intro c y hy
    have hi := mem_pick φ.isLB y
    have hj := mem_pick ψ.isLB y
    obtain ⟨a, ha⟩ := exists_unit_tv hp hp' _ _
    rw [c.chernDens_eq hψ hy hj, c.chernDens_eq hφ hy hi,
      hess_eq_of_unit c hφ hy hi hj a (key _ _ a ha)]
  refine ⟨ψ, hψ, ?_⟩
  rw [Weight.chernInt, Weight.chernInt, chernPart_eq_of_chernDens hd, chernPart_eq_of_chernDens hd]

theorem transport : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ),
    Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧
        ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y Δ L L' r r' hp hp' φ hφ
  exact exists_transport hp hp' φ hφ

end GlobalTheory.CompanionTheory.ChernTransport
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_presentation_transfer : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ), Presents Δ L r → Presents Δ L' r' → ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf → ∃ ψ : Weight Y.str (RingHom.id ℂ) L', ψ.IsCInf ∧ ψ.chernInt Y.dim Set.univ (fun _ => 1) = φ.chernInt Y.dim Set.univ (fun _ => 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ChernTransport.transport
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_presents (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ)
    (r' : L'.ι → Y.Fnˣ) (hL : Presents Δ L r) (hL' : Presents Δ L' r')
    (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L')
    (hφ : φ.IsCInf) (hψ : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨ψ₀, hψ₀, hmass⟩ := GlobalTheory.T.chern_integral_presentation_transfer Y Δ L L' r r' hL hL' φ hφ
  rw [← hmass]
  exact GlobalTheory.T.chern_integral_weight_indep Y L' ψ₀ ψ hψ₀ hψ

end GlobalTheory.CompanionTheory.ChernMass
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_presentation_indep : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L L' : LB Y.X) (r : L.ι → Y.Fnˣ) (r' : L'.ι → Y.Fnˣ), Presents Δ L r → Presents Δ L' r' → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) L'), φ.IsCInf → ψ.IsCInf → φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ChernMass.chernInt_eq_of_presents
end
