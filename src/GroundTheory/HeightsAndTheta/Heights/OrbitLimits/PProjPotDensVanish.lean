import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotDensVanish
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRankDropDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val →
    ∀ j, ∀ u ∈ (BV.chart j).target, ∀ p : (k : K) → ι k,
      (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ
        (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
          (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
          (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

theorem hessC_congr_of_eventuallyEq {D : ℕ} {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] ψ) : ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.fderiv
  unfold ReciprocityTheory.AnForm.hessC
  rw [h1.fderiv_eq]

theorem ProjRankDropDens.proof : ProjRankDropDens.Statement := by
  intro K _ ι _ P J n R L V BV hL hV j u hu p hp hrk
  set x : V := (BV.chart j).symm u with hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y => R.lift x.1 ((BV.chart j).symm y).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y q => G y q / G y ⟨q.1, p q.1⟩ with hτ
  obtain ⟨k₀, hk₀⟩ := R.A.cover x.1
  have hGa : ∀ q, AnalyticAt ℂ (fun y => G y q) u := by
    intro q
    have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y q) ∘ (R.A.chart k₀).symm) (R.A.chart k₀ x.1) :=
      R.holo x.1 q k₀ _ ⟨(R.A.chart k₀).map_source hk₀, by
        simp only [Set.mem_preimage, (R.A.chart k₀).left_inv hk₀]; exact R.mem_U _⟩
    have h2 : AnalyticAt ℂ (R.A.chart k₀ ∘ Subtype.val ∘ (BV.chart j).symm) u :=
      hV.2 j k₀ u ⟨hu, hk₀⟩
    refine (h1.comp_of_eq h2 rfl).congr ?_
    filter_upwards [holoMap_preimage_mem_nhds hV j k₀ hu hk₀] with y hy
    simp only [Function.comp_apply, G, (R.A.chart k₀).left_inv hy.2]
  have hc : ∀ᶠ y in 𝓝 u, ∀ k, G y ⟨k, p k⟩ ≠ 0 :=
    eventually_all.2 fun k => (hGa ⟨k, p k⟩).continuousAt.eventually_ne (hp k)
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun q => (hGa q).div (hGa ⟨q.1, p q.1⟩) (hp q.1)
  have hτ1 : ∀ y, (∀ k, G y ⟨k, p k⟩ ≠ 0) → ∀ k, τ y ⟨k, p k⟩ = 1 := fun y hy k => div_self (hy k)

  let E : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Nat.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Finite.equivFin (Σ k, ι k)).symm).toContinuousLinearEquiv
  let φ' : Fin n → (Fin (Nat.card (Σ k, ι k)) → ℂ) → ℝ := fun i z => Real.log ((L i).h (E.symm z))
  let τ' : (Fin n → ℂ) → (Fin (Nat.card (Σ k, ι k)) → ℂ) := ⇑E ∘ τ
  have hτ'a : AnalyticAt ℂ τ' u := (E.toContinuousLinearMap.analyticAt _).comp hτa
  have hφ' : ∀ i, ContDiffAt ℝ 2 (φ' i) (τ' u) := by
    intro i
    have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ u) :=
      Filter.mem_of_superset (eventually_all.2 fun k =>
        (continuous_apply (⟨k, p k⟩ : Σ k, ι k)).continuousAt.eventually_ne
          (show τ u ⟨k, p k⟩ ≠ 0 by rw [hτ1 u hp k]; exact one_ne_zero))
        fun z hz k => ⟨p k, hz k⟩
    have hlog : ContDiffAt ℝ ∞ (fun z => Real.log ((L i).h z)) (E.symm (τ' u)) := by
      simp only [τ', Function.comp_apply, E.symm_apply_apply]
      exact ((hL i).contDiffAt hS).log ((L i).pos _ fun k => ⟨p k, by rw [hτ1 u hp k]; exact one_ne_zero⟩).ne'
    exact (hlog.comp _ ((E.symm.contDiff (n := ∞)).restrict_scalars ℝ).contDiffAt).of_le
      (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

  let g : Fin n → (Fin n → ℂ) → ℂ := fun i y => ∏ k, G y ⟨k, p k⟩ ^ (L i).a k
  have hga : ∀ i, AnalyticAt ℂ (g i) u := fun i =>
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).zpow (hp k)
  have hg0 : ∀ i, g i u ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k)
  have hgerm : ∀ i, (fun y' => ((potOf R (L i)).pullback Subtype.val continuous_subtype_val).φ
      ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' i ∘ τ') y + Real.log ‖g i y‖ := by
    intro i
    filter_upwards [hc] with y hy
    show Real.log ((L i).h (G y)) = _
    have hGy : G y = fun q => G y ⟨q.1, p q.1⟩ * τ y q := by
      funext q
      simp only [τ]
      field_simp [hy q.1]
    have hs : (L i).h (G y) = (∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k) * (L i).h (τ y) := by
      conv_lhs => rw [hGy]
      exact (L i).smul (fun k => G y ⟨k, p k⟩) (τ y) hy
    have hpos : 0 < (L i).h (τ y) :=
      (L i).pos _ fun k => ⟨p k, by rw [hτ1 y hy k]; exact one_ne_zero⟩
    have hprod : 0 < ∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hy k)) _
    simp only [Function.comp_apply, φ', τ', E.symm_apply_apply, g, norm_prod, norm_zpow]
    rw [hs, Real.log_mul hprod.ne' hpos.ne', add_comm]
  have hrk' : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ' u).toLinearMap) < n := by
    have : LinearMap.range (fderiv ℂ τ' u).toLinearMap =
        (LinearMap.range (fderiv ℂ τ u).toLinearMap).map E.toLinearEquiv.toLinearMap := by
      rw [show τ' = ⇑E ∘ τ from rfl, E.comp_fderiv]
      exact LinearMap.range_comp (fderiv ℂ τ u).toLinearMap E.toLinearEquiv.toLinearMap
    rw [this, LinearEquiv.finrank_map_eq]
    exact hrk
  unfold locDens
  refine (maDens_congr_hessC _ (fun i => φ' i ∘ τ') u fun i => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt φ' τ' u hτ'a hφ' hrk')
  rw [hessC_congr_of_eventuallyEq (hgerm i)]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ (g i) u
    ((hφ' i).comp u (hτ'a.contDiffAt.restrict_scalars ℝ)) (hga i) (hg0 i)

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

theorem ProjPotDensVanish.proof : ProjPotDensVanish.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB hΨ j u hu hmax
  set x : V := (BV.chart j).symm u with hxdef
  have hx : x ∈ (BV.chart j).source := (BV.chart j).map_target hu
  have hxu : BV.chart j x = u := (BV.chart j).right_inv hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hΨ x.1 x.2)
  set G : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y => Ψ (segre (R.lift x.1 ((BV.chart j).symm y).1))
    with hG
  set τ : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y l => G y l / G y i with hτ
  have hGa : AnalyticAt ℂ G u := by
    have h := ProjRegular.proj_analyticAt Ψ hB x hx
    rwa [hxu] at h
  have hc : ∀ l, AnalyticAt ℂ (fun y => G y l) u := fun l => analyticAt_pi_iff.1 hGa l
  have hGi : G u i ≠ 0 := hi
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun l => (hc l).div (hc i) hGi
  have hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ u).toLinearMap) < n := by
    refine lt_of_le_of_ne ((LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun ℂ).le) ?_
    intro h
    apply hmax
    refine ⟨i, hi, j, hx, ?_⟩
    rw [hxu]
    exact h

  let φ' : (Fin (n + 1) → ℂ) → ℝ := fun w => Real.log (∑ l, ‖w l‖ ^ 2)
  have hsum_pos : ∀ w : Fin (n + 1) → ℂ, w i = 1 → 0 < ∑ l, ‖w l‖ ^ 2 := fun w hw =>
    lt_of_lt_of_le (by rw [hw]; norm_num)
      (Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i))
  have hτ1 : ∀ y, G y i ≠ 0 → τ y i = 1 := fun y hy => div_self hy
  have hφ' : ContDiffAt ℝ 2 φ' (τ u) :=
    ((ContDiff.sum fun l _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ l)).contDiffAt.log
      (hsum_pos _ (hτ1 u hGi)).ne')

  let g : (Fin n → ℂ) → ℂ := fun y => G y i ^ 2
  have hga : AnalyticAt ℂ g u := (hc i).pow 2
  have hg0 : g u ≠ 0 := pow_ne_zero 2 hGi
  have hev : ∀ᶠ y in 𝓝 u, G y i ≠ 0 := (hc i).continuousAt.eventually_ne hGi
  have hgerm : (fun y' => (projPot R Ψ V).φ ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' ∘ τ) y + Real.log ‖g y‖ := by
    filter_upwards [hev] with y hy
    show Real.log (∑ l, ‖G y l‖ ^ 2) = Real.log (∑ l, ‖τ y l‖ ^ 2) + Real.log ‖G y i ^ 2‖
    have hn : ‖G y i‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have hs : ∑ l, ‖G y l‖ ^ 2 = ‖G y i‖ ^ 2 * ∑ l, ‖τ y l‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [τ, norm_div, div_pow]
      field_simp
    rw [hs, norm_pow, Real.log_mul (pow_ne_zero 2 hn) (hsum_pos _ (hτ1 y hy)).ne', add_comm]
  unfold locDens
  refine (maDens_congr_hessC _ (fun _ => φ' ∘ τ) u fun _ => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt (fun _ => φ') τ u hτa (fun _ => hφ') hrk)
  refine (hessC_congr_of_eventuallyEq hgerm).trans ?_
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g u
    (hφ'.comp u (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0

end GroundTheory.Heights₂.Heights.Targets
end
end
