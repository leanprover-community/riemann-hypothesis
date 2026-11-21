import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedChartComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetric
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsConjInvariantMollifier
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialChartsWithRadii
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PotentialChartsRegularBound
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagHodgeStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.SymmetricChartsCutoffFamily
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedSettingSymmetricCharts

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_subsets_for_potential_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), IsSmoothHerm ref → ThRef M ref P.th → Adapted M P S → LogHom D ref.a w → ChartPsh D w → ChartCont D w → ChartBdd D w → ∃ B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData M.atlas, B.toPotentialCharts = P ∧ (∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), B.ph (M.proj z) = w z - Real.log (ref.h z)) ∧ (IsConjInvariantH ref → ConjOff D w → ∀ z ∈ mcPts (mCoordIdeal D.y), B.ph (M.proj (conjVec z)) = B.ph (M.proj z)) := by
  first | exact @LevelTowerAlt.potential_charts_regular_bound | exact LevelTowerAlt.potential_charts_regular_bound
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (κ : Equiv.Perm (Fin P.N)), SymmCharts M P κ → ∃ (cut : Fin P.N → M.Xc → ℝ) (C : ℝ), P.IsCutoffFamily cut C ∧ ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), cut (κ j) (M.proj (conjVec z)) = cut j (M.proj z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M P κ hS
  obtain ⟨hκ, -, hS3⟩ := hS
  choose g0 hg0s hg0b hg0one hg0c hg0t using fun j => LevelTowerAlt.exists_bumps P j
  have hstarMid : ∀ j t, t ∈ P.chartMid (κ j) → star t ∈ P.chartMid j := by
    intro j t ht
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨z, hz, hzx⟩ := M.surj ((P.chart (κ j)).symm t)
    obtain ⟨hsrc, hmid, -, hch⟩ := hS3 (κ j) z hz
    rw [hκ] at hsrc hmid hch
    have hx : M.proj z ∈ P.mid (κ j) := by
      rw [hzx]
      exact ht2
    have hx' : M.proj (conjVec z) ∈ P.mid j := hmid.2 hx
    have hxs : M.proj z ∈ (P.chart (κ j)).source := P.closure_mid _ (subset_closure hx)
    have hx's : M.proj (conjVec z) ∈ (P.chart j).source := P.closure_mid _ (subset_closure hx')
    have heq : P.chart j (M.proj (conjVec z)) = star t := by
      rw [hch hxs, hzx, (P.chart (κ j)).right_inv ht1]
    show star t ∈ (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact (P.chart j).map_source hx's
    · show (P.chart j).symm (star t) ∈ P.mid j
      rw [← heq, (P.chart j).left_inv hx's]
      exact hx'
  let g : Fin P.N → (Fin D.n → ℂ) → ℝ := fun j t => (g0 j t + g0 (κ j) (star t)) / 2
  have hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g j) := fun j =>
    ((hg0s j).add ((hg0s (κ j)).comp (LevelTowerAlt.contDiff_star _))).div_const 2
  have hbd : ∀ j y, 0 ≤ g j y ∧ g j y ≤ 1 := by
    intro j y
    have h1 := hg0b j y
    have h2 := hg0b (κ j) (star y)
    constructor
    · show 0 ≤ (g0 j y + g0 (κ j) (star y)) / 2
      linarith
    · show (g0 j y + g0 (κ j) (star y)) / 2 ≤ 1
      linarith
  have hone : ∀ j, ∀ x ∈ P.inner j, g j (P.chart j x) = 1 := by
    intro j x hx
    obtain ⟨z, hz, rfl⟩ := M.surj x
    obtain ⟨-, -, hinn, hch⟩ := hS3 j z hz
    have hmid : M.proj z ∈ P.mid j := P.closure_inner _ (subset_closure hx)
    have hsrc : M.proj z ∈ (P.chart j).source := P.closure_mid _ (subset_closure hmid)
    have h1 : g0 j (P.chart j (M.proj z)) = 1 := hg0one j _ ⟨_, subset_closure hx, rfl⟩
    have h2 : g0 (κ j) (star (P.chart j (M.proj z))) = 1 := by
      rw [← hch hsrc]
      exact hg0one (κ j) _ ⟨_, subset_closure (hinn.2 hx), rfl⟩
    show (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 = 1
    rw [h1, h2]
    norm_num
  have hK : ∀ j, tsupport (g j) ⊆ tsupport (g0 j) ∪ star '' tsupport (g0 (κ j)) := by
    intro j
    apply closure_minimal _ (((hg0c j).union ((hg0c (κ j)).image continuous_star)).isClosed)
    intro t ht
    rw [Function.mem_support] at ht
    by_cases h1 : g0 j t = 0
    · right
      refine ⟨star t, subset_tsupport _ ?_, star_star t⟩
      rw [Function.mem_support]
      intro h2
      apply ht
      show (g0 j t + g0 (κ j) (star t)) / 2 = 0
      rw [h1, h2]
      norm_num
    · left
      exact subset_tsupport _ h1
  have hcpt : ∀ j, IsCompact (tsupport (g j)) := fun j =>
    ((hg0c j).union ((hg0c (κ j)).image continuous_star)).of_isClosed_subset (isClosed_tsupport _) (hK j)
  have hsub : ∀ j, tsupport (g j) ⊆ P.chartMid j := by
    intro j t ht
    rcases hK j ht with h | ⟨u, hu, rfl⟩
    · exact hg0t j h
    · exact hstarMid j u (hg0t (κ j) hu)
  obtain ⟨C, hC⟩ := LevelTowerAlt.cutoff_of_bumps P g hsm hbd hone hcpt hsub
  refine ⟨_, C, hC, ?_⟩
  intro j z hz
  obtain ⟨hsrc, -, -, hch⟩ := hS3 j z hz
  simp only [ReciprocityTheory.AnForm.M.PLAux.chartPush]
  by_cases hx : M.proj z ∈ (P.chart j).source
  · rw [Set.indicator_of_mem (hsrc.2 hx), Set.indicator_of_mem hx]
    simp only [Function.comp]
    rw [hch hx]
    show (g0 (κ j) (star (P.chart j (M.proj z))) + g0 (κ (κ j)) (star (star (P.chart j (M.proj z))))) / 2 - 1
      = (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 - 1
    rw [hκ, star_star]
    ring
  · rw [Set.indicator_of_notMem (mt hsrc.1 hx), Set.indicator_of_notMem hx]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.symmetric_charts_of_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w) (κ : Equiv.Perm (Fin S'.B.N)), S'.IsTied → SymmCharts M S'.B.toPotentialCharts κ → (∀ v, S'.ρ.toFun (star v) = S'.ρ.toFun v) → (∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), S'.η (κ j) (M.proj (conjVec z)) = S'.η j (M.proj z)) → IsConjInvariantH S'.ref → (∀ z ∈ mcPts (mCoordIdeal D.y), S'.B.ph (M.proj (conjVec z)) = S'.B.ph (M.proj z)) → ConjU S' := by
  first | exact @LevelTowerAlt.tied_setting_symmetric_charts | exact LevelTowerAlt.tied_setting_symmetric_charts
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ => max t (C / Real.log t⁻¹ + C * t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => C / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have h2 := h0.max (h1.add (h0.const_mul C))
  simpa using h2

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w hL hP hC hB hO
  obtain ⟨ref, hra, hrs, hrc⟩ := GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric K J Hd.aMu
  obtain ⟨P, S, κ, hth, had, -, hsym, -⟩ :=
    GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii K J II Ψ Ω W D M ref (fun _ _ => 1) hrs hrc fun _ _ => one_pos
  obtain ⟨B, rfl, hph, hcj⟩ := GlobalTheory.CompanionTheory.Relay.adapted_subsets_for_potential_charts K J II Ψ Ω W D M ref w P S hrs hth had (hra ▸ hL) hP hC hB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier D.n
  obtain ⟨cut, Cη, hcut, hcc⟩ := GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric K J II Ψ Ω W D M _ κ hsym
  obtain ⟨C, t₀, ht₀, hcmp⟩ := GroundTheory.Heights₂.Heights.Regular.BoundedChartComparison.proof
    GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed
    GroundTheory.Heights₂.Heights.Regular.PolyMaxOscillation.proof_closed M.Xc D.n M.atlas B ρ
  let S' : BoundedRegularisationSetting M D.Xo Hd.aMu w :=
    { ref := ref, ref_deg := hra, ref_smooth := hrs, B := B, th_ref := hth, ph_eq := hph, ρ := ρ, «η» := cut,
      Cη := Cη, cutoff := hcut, e1 := fun t => max t (C / Real.log t⁻¹ + C * t),
      e1_ge := fun _ _ => le_max_left _ _ }
  have hT : S'.IsTied := by
    refine ⟨GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht j k x hx
    exact (hcmp t ht.1 ht.2 j k x hx).trans (le_max_right _ _)
  exact ⟨S', hT, GlobalTheory.CompanionTheory.Relay.symmetric_charts_of_regularization K J II Ψ Ω W D Hd M w S' κ hT hsym hρ hcc hrc (hcj hrc hO)⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.exists_regularization_setting
end
