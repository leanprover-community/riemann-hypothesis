import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotMassEq

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff

namespace ProjPotMassEq

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPotential_congr (A : FinHolAtlas e X) {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · rw [← hU x]
    exact (hP.1 x j).congr fun t ht => (hφ x _ ht.2).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2, hd z hz]

theorem mInt_congr (A : FinHolAtlas e X) (Φ Φ' : Fin e → LocPot X) (g : X → ℝ)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, g ((A.chart j).symm y) ≠ 0 →
      locDens A Φ j y = locDens A Φ' j y) : mInt A Φ g = mInt A Φ' g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ =>
      setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hg : g ((A.chart j).symm y) = 0
    · simp [hg]
    · rw [h j y hy hg]
  · rfl

theorem locDens_congr_germ (A : FinHolAtlas e X) (P Q : LocPot X) (j : Fin A.n) (y : Fin e → ℂ)
    (h : (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    locDens A (fun _ => P) j y = locDens A (fun _ => Q) j y :=
  ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun _ => h

theorem eventually_symm_mem (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {S : Set X} (hS : IsOpen S) (hyS : (A.chart j).symm y ∈ S) :
    ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ S :=
  ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hS.mem_nhds hyS)

theorem smooth_indicator (A : FinHolAtlas e X) {C : Set X} (hC : IsClopen C) {u : X → ℝ}
    (hu : A.Smooth u) : A.Smooth (C.indicator u) := by
  intro j t ht
  have hto : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 t := by
    simpa using (A.chart j).open_target.mem_nhds ht.1
  by_cases htC : (A.chart j).symm t ∈ C
  · refine (((hu j).contDiffAt hto).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.isOpen htC] with t' ht'
    simp [Set.indicator_of_mem ht']
  · refine ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_symm_mem A j ht.1 hC.compl.isOpen htC] with t' ht'
    simp [Set.indicator_of_notMem ht']

theorem massIndep_clopen [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {Φ : LocPot X}
    (hΦ : IsPotential A Φ) (Θ : LocPot X) (u : X → ℝ) (hu : A.Smooth u) {C : Set X}
    (hC : IsClopen C)
    (hΘ : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ C →
      locDens A (fun _ => Θ) j y = locDens A (fun _ => Φ + LocPot.ofFun u) j y) :
    mInt A (fun _ => Φ) (C.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Θ) (C.indicator fun _ => (1 : ℝ)) := by
  set w := C.indicator u with hw_def
  have hw : A.Smooth w := smooth_indicator A hC hu
  have hΦw : IsPotential A (Φ + LocPot.ofFun w) := isPotentialAdd A _ _ hΦ (isPotential_ofFun A w hw)
  have hg : Continuous (C.indicator fun _ : X => (1 : ℝ)) := hC.continuous_indicator continuous_const
  have hg' : Continuous (Cᶜ.indicator fun _ : X => (1 : ℝ)) :=
    hC.compl.continuous_indicator continuous_const
  have hsplit : (fun _ : X => (1 : ℝ)) = fun x =>
      1 * C.indicator (fun _ => (1 : ℝ)) x + Cᶜ.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx]
  have h1 := mIntLinear A (fun _ => Φ) (fun _ => hΦ) 1 _ _
    (mIntegrableCont A _ (fun _ => hΦ) _ hg) (mIntegrableCont A _ (fun _ => hΦ) _ hg')
  have h2 := mIntLinear A (fun _ => Φ + LocPot.ofFun w) (fun _ => hΦw) 1 _ _
    (mIntegrableCont A _ (fun _ => hΦw) _ hg) (mIntegrableCont A _ (fun _ => hΦw) _ hg')
  rw [← hsplit] at h1 h2
  have h3 : mInt A (fun _ => Φ + LocPot.ofFun w) (fun _ => 1) = mInt A (fun _ => Φ) (fun _ => 1) :=
    massIndep A (fun _ => Φ) (fun _ => w) (fun _ => hΦ) (fun _ => hw)
  have h4 : mInt A (fun _ => Φ + LocPot.ofFun w) (Cᶜ.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Φ) (Cᶜ.indicator fun _ => (1 : ℝ)) := by
    refine mInt_congr A _ _ _ fun j y hy hne => locDens_congr_germ A _ _ j y ?_
    have hyC : (A.chart j).symm y ∈ Cᶜ := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    filter_upwards [eventually_symm_mem A j hy hC.compl.isOpen hyC] with y' hy'
    show Φ.φ _ _ + w _ = Φ.φ _ _
    rw [hw_def, Set.indicator_of_notMem hy', add_zero]
  have h5 : mInt A (fun _ => Φ + LocPot.ofFun w) (C.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Θ) (C.indicator fun _ => (1 : ℝ)) := by
    refine mInt_congr A _ _ _ fun j y hy hne => ?_
    have hyC : (A.chart j).symm y ∈ C := by
      by_contra h
      exact hne (Set.indicator_of_notMem h _)
    rw [hΘ j y hy hyC]
    refine locDens_congr_germ A _ _ j y ?_
    filter_upwards [eventually_symm_mem A j hy hC.isOpen hyC] with y' hy'
    show Φ.φ _ _ + w _ = Φ.φ _ _ + u _
    rw [hw_def, Set.indicator_of_mem hy']
  linarith

end General

end ProjPotMassEq

end GroundTheory.Heights₂.Heights.Targets
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff

namespace ProjPotMassEq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}

omit [Fintype K] in

theorem blockSum_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))

theorem sqSum_pos {m : ℕ} {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) : 0 < ∑ l, ‖v l‖ ^ 2 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2) (Finset.single_le_sum (f := fun l => ‖v l‖ ^ 2)
    (fun l _ => by positivity) (Finset.mem_univ l))

def uFun (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (z : V) : ℝ :=
  (projPot R Ψ V).φ z z - (multiprojPot R V).φ z z

theorem projPot_eq (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (b z : V)
    (hzb : z.1 ∈ R.U b.1) (hz : Ψ (segre (R.lift z.1 z.1)) ≠ 0) :
    (projPot R Ψ V).φ b z = (multiprojPot R V).φ b z + uFun R Ψ V z := by
  obtain ⟨c, hc, hcz⟩ := R.compat b.1 z.1 z.1 ⟨hzb, R.mem_U z.1⟩
  have hm := (R.mem z.1 z.1 (R.mem_U z.1)).1
  have hc2 : ∀ k, ‖c k‖ ^ 2 ≠ 0 := fun k => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hS : ∀ k, ∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2 =
      ‖c k‖ ^ 2 * ∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2 := by
    intro k
    rw [hcz]
    simp [mul_pow, Finset.mul_sum]
  have hseg : segre (R.lift b.1 z.1) = (∏ k, c k) • segre (R.lift z.1 z.1) := by
    rw [hcz]
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  have hN : ∑ l, ‖Ψ (segre (R.lift b.1 z.1)) l‖ ^ 2 =
      ‖∏ k, c k‖ ^ 2 * ∑ l, ‖Ψ (segre (R.lift z.1 z.1)) l‖ ^ 2 := by
    rw [hseg, map_smul]
    simp [mul_pow, Finset.mul_sum]
  have hsum : ∑ k, Real.log (∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (‖c k‖ ^ 2) + ∑ k, Real.log (∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [hS k, Real.log_mul (hc2 k) (blockSum_pos hm k).ne']
  have hprod : Real.log (‖∏ k, c k‖ ^ 2) = ∑ k, Real.log (‖c k‖ ^ 2) := by
    rw [norm_prod, ← Finset.prod_pow, Real.log_prod fun k _ => hc2 k]
  simp only [uFun, projPot, multiprojPot]
  rw [hN, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => hc k))) (sqSum_pos hz).ne', hsum, hprod]
  ring

theorem isPotential_multiprojPot {V : Set R.X} {BV : FinHolAtlas n V}
    (hH : HoloMap BV R.A Subtype.val) : IsPotential BV (multiprojPot R V) := by
  refine isPotential_congr BV (P := (potOf R (HermLine.sqMetric (fun _ => 2))).pullback
    Subtype.val hH.1) (fun _ => rfl) (fun x z hz => ?_)
    (isPotentialPullback R.A BV Subtype.val hH _
      (isPotential_potOf R (isSmoothHerm_sqMetric _)))
  have hm := (R.mem x.1 z.1 hz).1
  show Real.log (∏ k, Real.sqrt (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2) ^ 2) =
    ∑ k, Real.log (∑ i, ‖R.lift x.1 z.1 ⟨k, i⟩‖ ^ 2)
  rw [Finset.prod_congr rfl fun k _ => Real.sq_sqrt (by positivity),
    Real.log_prod fun k _ => (blockSum_pos hm k).ne']

theorem smooth_uFun (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X}
    {BV : FinHolAtlas n V} (hH : HoloMap BV R.A Subtype.val)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) : BV.Smooth (uFun R Ψ V) := by
  intro j t ht
  set x : V := (BV.chart j).symm t with hx_def
  have hxs : x ∈ (BV.chart j).source := (BV.chart j).map_target ht.1
  have htx : BV.chart j x = t := (BV.chart j).right_inv ht.1
  have hF := ProjRegular.proj_analyticAt Ψ hH x hxs
  have hU := (ProjRegular.lift_analyticAt hH x hxs).2
  rw [htx] at hF hU

  have hp : ContDiffAt ℝ ∞ (fun t' => (projPot R Ψ V).φ x ((BV.chart j).symm t')) t := by
    have hsq : ContDiffAt ℝ ∞ (fun t' => ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t').1)) l‖ ^ 2) t :=
      ContDiffAt.sum fun l _ =>
        (((analyticAt_pi_iff.1 hF l).contDiffAt).restrict_scalars ℝ).norm_sq ℝ
    have hne : ∑ l, ‖Ψ (segre (R.lift x.1 ((BV.chart j).symm t).1)) l‖ ^ 2 ≠ 0 :=
      (sqSum_pos (hΨ x.1 x.2)).ne'
    exact hsq.log hne

  have hm : ContDiffAt ℝ ∞ (fun t' => (multiprojPot R V).φ x ((BV.chart j).symm t')) t :=
    ((isPotential_multiprojPot hH).1 x j).contDiffAt
      (((BV.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x.1).preimage
        continuous_subtype_val)).mem_nhds ⟨ht.1, R.mem_U x.1⟩)
  refine ((hp.sub hm).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU] with t' ht'
  have := projPot_eq Ψ x ((BV.chart j).symm t') ht' (hΨ _ ((BV.chart j).symm t').2)
  simp only [Function.comp_apply]
  linarith

theorem proof : ProjPotMassEq.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hV hΨ C hC
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  refine massIndep_clopen BV (isPotential_multiprojPot hH) (projPot R Ψ V) (uFun R Ψ V)
    (smooth_uFun Ψ hH hΨ) hC fun j t ht _ => locDens_congr_germ BV _ _ j t ?_
  have hxs : (BV.chart j).symm t ∈ (BV.chart j).source := (BV.chart j).map_target ht
  have hU := (ProjRegular.lift_analyticAt hH ((BV.chart j).symm t) hxs).2
  rw [(BV.chart j).right_inv ht] at hU
  filter_upwards [hU] with t' ht'
  exact projPot_eq Ψ _ _ ht' (hΨ _ ((BV.chart j).symm t').2)

end ProjPotMassEq

end GroundTheory.Heights₂.Heights.Targets
end
end
