import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · simp [hr, loc, ht, dens_zero]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end

section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  first | exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | exact GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | (intros; apply GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
end
end

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero : ∀ {n : ℕ} (F : V n → GlobalTheory.CxForm.Alt n), (∀ S, ContDiff ℝ 1 (fun v => (GlobalTheory.CxForm.bas n).repr (F v) S)) → HasCompactSupport F → ∫ v, (GlobalTheory.CxForm.dens (GlobalTheory.CxForm.dbarAt F v)).re = 0 := by
  atlas_forward_decl GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have calc0 := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0
  have hP : A.IsForm (A.fn χ * γ) := (calc0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) := (calc0 _ _ hP hγ).2.2.2.2.1

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dif_neg ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  atlas_forward_decl GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  have h0 : A.IsForm 0 := by simpa using (C.2.1 0 1 1 C.1 C.1).2.2.1
  have hd0 : A.dbar 0 = 0 := by
    have := (C.2.1 0 0 0 h0 h0).2.2.2.2.2.2.1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have key : ∀ s : Finset (Fin N), A.IsForm (∑ j ∈ s, α j) ∧ A.dbar (∑ j ∈ s, α j) = ∑ j ∈ s, A.dbar (α j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using ⟨h0, hd0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := C.2.1 0 (α a) _ (hα a) ih.1
      exact ⟨this.1, by rw [this.2.2.2.2.2.2.1, ih.2]⟩
  exact (key Finset.univ).2
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    (C.2.1 0 _ _ (HolAtlas.isForm_fn A (hs j)) hη).2.1
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
end
