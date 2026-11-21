import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPush
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.comp' (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.comp' (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_homogeneous_potential : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem isFlatOn_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  intro K _ J _ P Jd D R Ψ N T hT a x _
  cases a with
  | none =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩
    simp [potOf, corr, Top.trivLine, LocPot.ofFun]
  | some r =>
    choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)
    refine ⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo),
      ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩
    · have hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w := fun k _ =>
        hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩
      exact (Finset.analyticAt_fun_sum _ hs).neg
    · have hm := (R.mem x y hy.1).1
      have e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y)) :=
        log_stepLine (fun k => T (r.1, k)) r.2 hm
      have e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re := fun k => by
        simpa [potOf, LocPot.ofFun] using hE k y (Set.mem_iInter.1 hy.2 k)
      simp [e, e', LocPot.ofFun]

end GlobalTheory.CompanionTheory.Ar.Chg
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_on_log_resolution_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_potential_pullback : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | exact GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ) (R₀ : AnLogRes (mCoordIdeal y₀) ⊤ D) (R : AnLogRes (mCoordIdeal y) ⊤ D) (h : R.X → R₀.X), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (blkV bk bx p))) → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ br : Set R₀.X, IsDegreeOff R₀.A R.A h d br := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block | exact GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isDegreeOff_of_block <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DegComp

theorem det_ne_zero_of_injective {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hπ : HoloMap B A π)
    (hinj : Function.Injective π) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : π ((B.chart j).symm y) ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hπ.1)
  have hI : Set.InjOn (A.chart k ∘ π ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) := by
    intro a ha b hb hab
    exact (B.chart j).symm.injOn ha.1 hb.1 (hinj ((A.chart k).injOn ha.2 hb.2 hab))
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn e _ (A.chart k ∘ π ∘ (B.chart j).symm) hU
    (fun w hw => (hπ.2 j k w hw).differentiableAt.differentiableWithinAt) hI y ⟨hy, hk⟩
  intro h0
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero h0
  have hker : LinearMap.ker (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  rw [hker] at hlt
  exact lt_irrefl _ hlt

theorem isDegreeOff_one_of_bijective {e : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X}
    (hπ : HoloMap B A π) (hbij : Function.Bijective π) : IsDegreeOff A B π 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · simpa using isAnalyticSubset_empty B
  · simp
  · intro x _
    obtain ⟨y, rfl⟩ := hbij.2 x
    have hfib : π ⁻¹' {π y} = {y} := by
      ext z
      simp [hbij.1.eq_iff]
    rw [hfib, Set.ncard_singleton]
  · intro j k y hy _ hk
    exact det_ne_zero_of_injective hπ hbij.1 j k hy hk

theorem holoMap_comp_isDegreeOff : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  intro e d X Y Z _ _ _ _ _ _ A B C π h br hπ hbij hh hd
  obtain ⟨g, hgl, hgr, hg⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one A B π hπ
    (isDegreeOff_one_of_bijective hπ hbij)
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, ?_⟩
  obtain ⟨han, hint, hpan, hpint, hfib, hdet⟩ := hd
  have hpre : (π ∘ h) ⁻¹' (π '' br) = h ⁻¹' br := by
    ext z
    simp [hbij.1.mem_set_image]
  have himg : π '' br = g ⁻¹' br := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hgl] using hy
    · intro hx
      exact ⟨g x, hx, hgr x⟩
  let E : Y ≃ₜ X :=
    { toFun := π, invFun := g, left_inv := hgl, right_inv := hgr,
      continuous_toFun := hπ.1, continuous_invFun := hg.1 }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    intro x
    obtain ⟨W, hW, hxW, r, f, hf, hS⟩ := han (g x)
    refine ⟨g ⁻¹' W, hW.preimage hg.1, hxW, r, fun i => f i ∘ g,
      fun i => GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_comp hg (hf i), ?_⟩
    ext y
    simpa using Set.ext_iff.1 hS (g y)
  · change interior (E '' br) = ∅
    rw [← E.image_interior, hint, Set.image_empty]
  · rw [hpre]
    exact hpan
  · rw [hpre]
    exact hpint
  · intro x hx
    have hgx : g x ∉ br := fun hb => hx ⟨g x, hb, hgr x⟩
    have hset : (π ∘ h) ⁻¹' {x} = h ⁻¹' {g x} := by
      ext z
      constructor
      · intro hz
        have hz' : π (h z) = x := hz
        change h z = g x
        rw [← hz', hgl]
      · intro hz
        have hz' : h z = g x := hz
        change π (h z) = x
        rw [hz', hgr]
    rw [hset]
    exact hfib _ hgx
  · intro j k y hy hnot hk
    have hnot' : (C.chart j).symm y ∉ h ⁻¹' br := by rwa [hpre] at hnot
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp]
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact det_ne_zero_of_injective hπ hbij.1 l k hQt hk'
    · rw [hQdef]
      exact hdet j l y hy hnot' hl

end GlobalTheory.CompanionTheory.Ar.DegComp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_composition : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgLie

section Modules

theorem mem_of_mem_iSup {Ω E I : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω)
    (W : I → Submodule Ω E) (hW : iSupIndep W) (N : I → Submodule A E) (hN : ∀ s, ∀ x ∈ N s, x ∈ W s)
    {e : E} (s₀ : I) (he : e ∈ ⨆ s, N s) (hs : e ∈ W s₀) : e ∈ N s₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp N e).1 he
  have hsum : (f.sum fun _ x => x) - f s₀ = ∑ i ∈ f.support.erase s₀, f i := by
    by_cases h0 : s₀ ∈ f.support
    · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0]
      abel
    · rw [Finsupp.sum, Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  have h1 : (f.sum fun _ x => x) - f s₀ ∈ W s₀ := sub_mem hs (hN _ _ (hf s₀))
  have h2 : (f.sum fun _ x => x) - f s₀ ∈ ⨆ (k) (_ : k ≠ s₀), W k := by
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hk) (hN _ _ (hf k)))
  have h3 := (Submodule.disjoint_def.1 (hW s₀)) _ h1 h2
  rw [sub_eq_zero.1 h3]
  exact hf s₀

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (e : E) : e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

end Modules

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem not_inFibre_push {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀}
    {i : Ω₀ →+* Ω} (hξ : IsCptGen ξ) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i) (q : Cpt ξ) {r : ℕ}
    (hq : ¬ InFibre ξ r q) : ¬ InFibre ξ₀ r (pushCpt hd q) := by
  intro hf
  apply hf
  obtain ⟨h0, -, s, hs⟩ : unitAt ξ q (r : Ω) := not_not.1 hq
  have hmul : (r : X.presheaf.stalk q.1) * s = 1 := hξ.inj q (by
    rw [map_mul, map_one, map_natCast, hs]
    exact mul_inv_cancel₀ h0)
  have hu : IsUnit (r : X.presheaf.stalk q.1) := IsUnit.of_mul_eq_one _ hmul
  have hu₀ : IsUnit (r : X₀.presheaf.stalk (h q.1)) :=
    isUnit_of_map_unit (h.stalkMap q.1).hom _ (by rwa [map_natCast])
  have h0' : (r : Ω₀) ≠ 0 := fun e => h0 (by rw [← map_natCast i, e, map_zero])
  refine ⟨h0', ⟨_, map_natCast (genMap ξ₀ (pushCpt hd q)) r⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu₀
  refine ⟨(u⁻¹ : (X₀.presheaf.stalk (h q.1))ˣ).val, ?_⟩
  have e1 : genMap ξ₀ (pushCpt hd q) u.val = (r : Ω₀) := (congrArg _ hu').trans (map_natCast _ r)
  exact (map_units_inv (genMap ξ₀ (pushCpt hd q)) u).trans (congrArg Inv.inv e1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_inj_of_pull {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) {ξ : Spec (CommRingCat.of Ω) ⟶ S'} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G' ξ V) {e e' : V}
    (h : (M.pt e).left ≫ φ = (M.pt e').left ≫ φ) : e = e' :=
  M.inj (Over.OverMorphism.ext (hG.1.hom_ext h ((Over.w _).trans (Over.w _).symm)))

theorem exists_value_up {t : SAB H X₀} {t' : SAB H X} {f : X ⟶ X₀} (m : SABMap t' t f)
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {i : Ω₀ →+* Ω}
    (hall : ∀ q : X, genPt ξ ⤳ q) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] {M : LieModel t.G ξ₀ V} {M' : LieModel t'.G ξ V'} {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) {e : V} {v₀ : epsAt (z ≫ f) ⟶ t.G} (hv : M.ValAt (z ≫ f) e v₀) :
    ∃ v : epsAt z ⟶ t'.G, M'.ValAt z (j e) v ∧ v₀.left = v.left ≫ m.φ := by
  obtain ⟨h₀, w, hw, hwz⟩ := hv
  have hp : genPt ξ₀ ⤳ f (centre z) := h₀
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap (centre z)).hom) ≫ X₀.fromSpecStalk (f (centre z)) =
      X.fromSpecStalk (centre z) ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ ⟨centre z, hall _⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ₀ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ (hall _) hp)
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨centre z, hall _⟩
  obtain ⟨u, hu, huφ⟩ := LiePull.ext_up (A := X₀.presheaf.stalk (f (centre z))) (A' := X.presheaf.stalk (centre z))
    (g := genMap ξ₀ ⟨f (centre z), hp⟩) (g' := genMap ξ ⟨centre z, hall _⟩) (ρ := (f.stalkMap (centre z)).hom)
    (x := X₀.fromSpecStalk (f (centre z))) (x' := X.fromSpecStalk (centre z)) (M := M) (M' := M') (j := j) m.cart hj hρ
    hρ' hx' hw
  have hc : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨LieCarrier.epsHom _ _ z hc ≫ u, ⟨hall _, u, hu, rfl⟩, ?_⟩
  have e1 : (LieCarrier.epsHom _ _ z hc ≫ u).left =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ u.left := rfl
  have e2 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have e4 : spMap (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom) =
      spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ spMap (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e2]
    exact (congrArg spMap (LiePull.dualMap_comp (f.stalkMap (centre z)).hom (Scheme.stalkClosedPointTo z).hom).symm).trans
      (spMap_comp' _ _)
  have e3 : (LieCarrier.epsHom _ _ z hc ≫ u).left ≫ m.φ = spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
      spMap (dualMap (f.stalkMap (centre z)).hom) ≫ w.left :=
    (congrArg (· ≫ m.φ) e1).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ ·) huφ))
  exact hwz.trans (((congrArg (· ≫ w.left) e4).trans (Category.assoc _ _ _)).trans e3.symm)

end Points

section Main

theorem lie_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl hβ hcov hfl
  obtain ⟨-, hf, hcst⟩ := hcov
  obtain ⟨m₀, hφ⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  obtain ⟨j, hpt, hsemi, hind, -, hpull⟩ := GlobalTheory.T.lie_model_dominant_hodge E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ Ω₀ Ω 𝔐₀.ξ 𝔐.ξ i 𝔐₀.Li 𝔐.Li 𝔐₀.M 𝔐.M
    𝔐₀.tie.gen 𝔐.tie.gen hd
  have hact : ∀ a e, 𝔐.ρ a (j e) = j (𝔐₀.ρ a e) := fun a e => pt_inj_of_pull m₀.cart 𝔐.M (by
    have e1 := congrArg CommaMorphism.left (𝔐.act a (j e))
    have e2 := congrArg CommaMorphism.left (𝔐₀.act a e)
    have e3 := m₀.act a
    rw [hpt]
    refine (congrArg (· ≫ m₀.φ) e1).trans ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (_ ≫ ·) e3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (𝔐₀.t.act.act a).left) (hpt e)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (spMap (dualMap i) ≫ ·) e2.symm)
  have hemb : ∀ s, 𝔐.emb s = i.comp (𝔐₀.emb s) := fun s => by
    simp only [HodgeCpt.emb, hcst, RingHom.comp_assoc]
  have heig : ∀ s e, e ∈ 𝔐₀.Vgen s → j e ∈ 𝔐.Vgen s := fun s e he => by
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [hact, (mem_eigSp_iff _ _ _).1 he a, hsemi, hemb]
    rfl
  refine ⟨j, hsemi, hind, fun s a => ?_, fun q hq s => ?_, fun z r b Γ hΓ => ?_⟩
  · refine pt_inj_of_pull 𝔐.m.cart 𝔐.M ?_
    have e1 : (𝔐.M.pt (j (Fl₀.b s a))).left ≫ 𝔐.m.φ =
        spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ := by
      rw [hφ, ← Category.assoc, hpt, Category.assoc]
    exact e1.trans (hfl s a).symm
  · have hq₀ : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐₀.ξ r (pushCpt hd q) :=
      fun r hr => not_inFibre_push 𝔐.tie.gen hd q (hq r hr)
    obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y 𝔐 hβ q hq
    obtain ⟨hV₀, -, hlat₀⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ (pushCpt hd q) hq₀
    obtain ⟨-, -, -, -, -, -, hindep, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
    rw [hV s, hV₀ s]
    let N : (CMType H ⊕ CMType H) → Submodule (regAt 𝔐.ξ q) 𝔐.Li := fun s' =>
      Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.dR s' (pushCpt hd q) : Set 𝔐₀.Li))
    have hle : ∀ s', N s' ≤ 𝔐.dR s' q := fun s' => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, heig s' e he.2⟩
      rw [hpull]
      exact Submodule.subset_span ⟨hd.specializes q, e, he.1, rfl⟩
    have htop : 𝔐.M.lat q ≤ ⨆ s', N s' := by
      rw [hpull]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ ⨆ s', 𝔐₀.dR s' (pushCpt hd q) := hlat₀ ▸ he
      refine Submodule.iSup_induction _ (motive := fun x => j x ∈ ⨆ s', N s') he' (fun s' x hx => ?_) ?_ ?_
      · exact Submodule.mem_iSup_of_mem s' (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x x' hx hx'
        rw [map_add]
        exact Submodule.add_mem _ hx hx'
    refine le_antisymm (fun e he => ?_) (hle s)
    exact mem_of_mem_iSup _ 𝔐.Vgen hindep N (fun s' x hx => (hle s' hx).2) s (htop he.1) he.2
  · obtain ⟨v₀, hv₀, hIP⟩ := hΓ
    choose v hv hvφ using fun k => exists_value_up m₀ 𝔐.all hd hpt z (hv₀ k)
    exact ⟨v, hv, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ z (v p) (v q) (v₀ p) (v₀ q) (Γ p q) (hvφ p) (hvφ q)).2 (hIP p q)⟩

end Main

end GlobalTheory.CompanionTheory.Ar.ChgLie
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GP

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_coeff {r : ℕ} (b b₀ : Fin r → E) (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i)
    (hli : LinearIndependent Ω b) (i : Fin r) :
    ∃ t : Ω, t ≠ 0 ∧ b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i := by
  have hni : b i ∉ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := hli.notMem_span_image (by simp)
  have h1 : b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ (i+1) := by rw [← h]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [GlobalTheory.CompanionTheory.Ar.Flag.step_succ] at h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have ht : t ≠ 0 := by rintro rfl; apply hni; rw [h, ← hyz]; simpa using hy
  exact ⟨t, ht, by rw [← hyz]; simpa using hy⟩

theorem gr_isGen_of_frame (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ)
    (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) (hb : L.IsFrameAt b p) (i : Fin r) {t : Ω}
    (ht : t ≠ 0) (hy : b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p t := by
  refine ⟨ht, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro s ⟨e, he, hs⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have h2 : (∑ k, c k • b k) - (s / t) • b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := by
      rw [h]
      have : (∑ k, c k • b k) - (s / t) • b i =
          ((∑ k, c k • b k) - s • b₀ i) - (s / t) • (b i - t • b₀ i) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht]; abel
      rw [this]; exact sub_mem hs (Submodule.smul_mem _ _ hy)
    obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[Ω] Ω, ∀ k, φ (b k) = if k = i then 1 else 0 := by
      obtain ⟨g, hg⟩ := (Fintype.linearCombination Ω b).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro m hm; funext k; exact Fintype.linearIndependent_iff.1 hb.1 m (by simpa [Fintype.linearCombination_apply] using hm) k))
      refine ⟨(LinearMap.proj i).comp g, fun k => ?_⟩
      have := LinearMap.congr_fun hg (Pi.single k 1)
      simp [Fintype.linearCombination_apply_single] at this
      simp [this, Pi.single_apply, eq_comm]
    have h3 : GlobalTheory.CompanionTheory.Ar.flagStep Ω b i ≤ LinearMap.ker φ := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have : k ≠ i := by rintro rfl; simp at hk
      simp [hφ, this])
    have h4 := h3 h2
    have h5 : ∀ k, φ (c k • b k) = (c k : Ω) * φ (b k) := fun k => φ.map_smul (c k : Ω) (b k)
    simp only [LinearMap.mem_ker, map_sub, map_sum, h5, map_smul, hφ] at h4
    simp at h4
    refine Submodule.mem_span_singleton.2 ⟨c i, ?_⟩
    show (c i : Ω) * t = s
    rw [sub_eq_zero.1 h4, div_mul_cancel₀ _ ht]
  · rintro _ rfl
    exact ⟨b i, by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩, hy⟩

theorem gen_ratio {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    ∃ u : Ω, u ∈ regAt ξ p ∧ u⁻¹ ∈ regAt ξ p ∧ s = u * t := by
  have a1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self _
  have a2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs.2, ht.2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 a2
  have hu' : (u : Ω) * t = s := hu
  have hv' : (v : Ω) * s = t := hv
  have e : (v : Ω) * (u : Ω) = 1 := by
    refine mul_right_cancel₀ ht.1 ?_
    rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
  refine ⟨u, u.2, ?_, hu'.symm⟩
  rw [← eq_inv_of_mul_eq_one_left e]
  exact v.2

theorem gen_mul {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {t u : Ω} (h : Λ.IsGenAt p t) (h0 : u ≠ 0)
    (hu : u ∈ regAt ξ p) (hu' : u⁻¹ ∈ regAt ξ p) : Λ.IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero h0 h.1, ?_⟩
  rw [h.2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u⁻¹, hu'⟩, inv_mul_cancel_left₀ h0 _⟩
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

end Frames

section Pull

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {E E₀ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₀] [Module Ω₀ E₀]

theorem mem_flagStep_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {y : Fin r → E₀} {n : ℕ} {x : E₀} (hx : x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    j x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_pull_le {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {x y : Fin r → E₀} {n : ℕ} (h : GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ x n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (x k)) n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_flagStep_pull hj (h (Submodule.subset_span ⟨k, hk, rfl⟩))

theorem isFrameAt_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀))) {r : ℕ} {b : Fin r → E₀}
    (hb : L₀.IsFrameAt b p₀) : L.IsFrameAt (fun k => j (b k)) p := by
  refine ⟨hli _ _ hb.1, ?_⟩
  rw [hL]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ L₀ p₀ := he
    rw [hb.2] at he'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    rw [map_sum]
    refine sum_mem fun k _ => ?_
    have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ p) • j (b k) := hj (c k : Ω₀) (b k)
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    refine ⟨b k, ?_, rfl⟩
    show b k ∈ L₀ p₀
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem isGenAt_pull (i : Ω₀ →+* Ω) (j : E₀ →+ E) {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    {r : ℕ} {c₀ : Fin r → E₀} {c : Fin r → E} (hc : ∀ a, j (c₀ a) = c a)
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀)))
    (hf : L₀.IsFlagVBOn Set.univ c₀) (a : Fin r) {t₀ : Ω₀} (h : (L₀.gr c₀ a).IsGenAt p₀ t₀) :
    (L.gr c a).IsGenAt p (i t₀) := by
  obtain ⟨U, hU, b₁, hb, hfr⟩ := hf p₀ trivial
  have hfr' := hfr p₀ trivial hU
  obtain ⟨t₁, ht₁, hy⟩ := exists_coeff b₁ c₀ hb hfr'.1 a
  have g₁ := gr_isGen_of_frame L₀ b₁ c₀ p₀ hb hfr' a ht₁ hy
  obtain ⟨u, hu, hu', rfl⟩ := gen_ratio h g₁
  have hc' : c = fun k => j (c₀ k) := funext fun a => (hc a).symm
  subst hc'
  have hframe : L.IsFrameAt (fun k => j (b₁ k)) p := isFrameAt_pull hreg hj hli hL hfr'
  have hadapt : ∀ n, GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (b₁ k)) n = GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) n :=
    fun n => le_antisymm (flagStep_pull_le hj (hb n).le) (flagStep_pull_le hj (hb n).ge)
  have hy' : j (b₁ a) - i t₁ • j (c₀ a) ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) a := by
    have := mem_flagStep_pull hj hy
    rwa [map_sub, hj] at this
  have g := gr_isGen_of_frame L (fun k => j (b₁ k)) (fun k => j (c₀ k)) p hadapt hframe a
    ((map_ne_zero i).2 ht₁) hy'
  have hu0 : u ≠ 0 := left_ne_zero_of_mul h.1
  rw [map_mul]
  refine gen_mul g ((map_ne_zero i).2 hu0) (hreg _ hu) ?_
  rw [← map_inv₀]
  exact hreg _ hu'

end Pull

theorem genPull_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hr hj hli hb hV
  intro q hq s a t₀ hg
  exact isGenAt_pull i j (hr q) hj hli (hb s) (hV q hq s) (Fl₀.sub s) a hg

end GlobalTheory.CompanionTheory.Ar.Chg.GP
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem normPull_of_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hc hreg hsl hli hfl hst hgr
    z s a t₀ ν hN
  obtain ⟨hh, b, Γ, hfs, hfr, hb, hG, hP, rfl⟩ := hN
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hbase : Fl.b s = fun k => j (Fl₀.b s k) := funext fun k => (hfl s k).symm
  have hnf : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r ⟨centre z, hq⟩ := fun r hr => not_inFibre 𝔐.ξ z hq hr
  have hV := hst ⟨centre z, hq⟩ hnf s
  have hpush : (⟨centre (z ≫ h), hh⟩ : Cpt 𝔐₀.ξ) = pushCpt hd ⟨centre z, hq⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply z h _)
  have hfr' : (𝔐₀.V s).IsFrameAt b (pushCpt hd ⟨centre z, hq⟩) := hpush ▸ hfr
  refine ⟨hq, fun k => j (b k), Γ, fun s' => ?_, ⟨hli _ b hfr.1, ?_⟩, ?_, hgr z _ b Γ hG, hP, rfl⟩
  · rw [hbase]
    exact FlagPull.flagStep_map_eq hsl hfs s'
  · rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩) := he
      rw [hfr'.2] at he'
      clear he
      show j e ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hq⟩) (Set.range fun k => j (b k))
      induction he' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul u x _ hx =>
        have e1 : j (u • x) = (⟨i u, hreg _ _ u.2⟩ : regAt 𝔐.ξ ⟨centre z, hq⟩) • j x := hsl (u : Ω₀) x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    · rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨b k, ?_, rfl⟩
      show b k ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩)
      rw [hfr'.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · have hm := FlagPull.map_mem_flagStep hsl (Fl₀.b s) a hb
    rw [map_sub, hsl, hfl, ← hbase] at hm
    exact hm

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | exact GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Ratio

open MvPolynomial

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
  [∀ k, Fintype (J k)] {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem prod_comp_zpow {G : Type} [CommGroupWithZero G] {bk : K₀ → K} (hbk : Function.Injective bk) (c : K → G)
    (a₀ : K₀ → ℤ) : ∏ k, c (bk k) ^ a₀ k = ∏ k, c k ^ pullDeg bk a₀ k := by
  classical
  have h1 : ∏ k, c k ^ pullDeg bk a₀ k = ∏ k ∈ Finset.univ.image bk, c k ^ pullDeg bk a₀ k := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
    have : ¬ ∃ x, bk x = k := fun ⟨x, hx⟩ => hk (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)
    simp [pullDeg, Function.extend_apply' _ _ _ this]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hbk h]
  exact Finset.prod_congr rfl fun k _ => by simp [pullDeg, hbk.extend_apply]

def cmpFn (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) : Ω :=
  i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)

def cmpVal (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (w : (Σ k, J k) → ℂ)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ) : ℂ :=
  u * (∏ k, w ⟨k, c k⟩ ^ a k) / ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k

def IsCmp (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k))
    (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (w : (Σ k, J k) → ℂ) (t : ℂ) : Prop :=
  ∃ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
    (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) ∧ u ≠ 0 ∧
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) w u ∧
    t = cmpVal bk bx a a₀ w c c₀ u

theorem cmpVal_ne_zero {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} {c₀ : (k : K₀) → J₀ k} {u : ℂ} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (hu : u ≠ 0) : cmpVal bk bx a a₀ w c c₀ u ≠ 0 :=
  div_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)))
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))

section Val

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_prod_zpow {I : Type} [Fintype I] {f : I → Ω} {r : I → ℂ} (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ValAt ξ z (f k) (r k)) (h0 : ∀ k, r k ≠ 0) (n : I → ℤ) :
    ValAt ξ z (∏ k, f k ^ n k) (∏ k, r k ^ n k) := by
  classical
  have hp : ∀ s : Finset I, ValAt ξ z (∏ k ∈ s, f k ^ n k) (∏ k ∈ s, r k ^ n k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (h k) (h0 k) _) ih
  exact hp Finset.univ

theorem cmpVal_eq {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {bk : K₀ → K}
    {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀} {w : (Σ k, J k) → ℂ}
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    {c c' : (k : K) → J k} {c₀ c₀' : (k : K₀) → J₀ k} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0) (h1' : ∀ k, w ⟨k, c' k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (h2' : ∀ k, w (blkV bk bx ⟨k, c₀' k⟩) ≠ 0) {u u' : ℂ}
    (hu : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u) (hu' : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c' c₀') u') :
    cmpVal bk bx a a₀ w c c₀ u = cmpVal bk bx a a₀ w c' c₀' u' := by
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (h1 k))).1
  have hyc' : ∀ k, y ⟨k, c' k⟩ ≠ 0 := fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).1
  have hyv : ∀ k, y (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).1
  have hyv' : ∀ k, y (blkV bk bx ⟨k, c₀' k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀' k)) (IsUnit.mk0 _ (h2' k))).1
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).2 (c k)
  choose q hq hq' using fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).2 (bx k (c₀' k))
  have hr0 : ∀ k, r k ≠ 0 := fun k h => h1 k (by rw [hr', h, zero_mul])
  have hq0 : ∀ k, q k ≠ 0 := fun k h => h2' k (by
    show w ⟨bk k, bx k (c₀' k)⟩ = 0
    rw [hq', h, zero_mul])
  have e1 := valAt_prod_zpow hz hr hr0 a
  have e2 := valAt_prod_zpow hz hq hq0 a₀
  have hM : ∀ c₁ : (k : K₀) → J₀ k, i (∏ k, y₀ ⟨k, c₁ k⟩ ^ a₀ k) = ∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k := by
    intro c₁
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀]
    show _ = y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k
    rw [hy]
  have key : cmpFn i y₀ y a a₀ e e₀ c' c₀' = cmpFn i y₀ y a a₀ e e₀ c c₀ *
      (∏ k, (y ⟨bk k, bx k (c₀' k)⟩ / y ⟨bk k, bx k (c₀ k)⟩) ^ a₀ k) *
      ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ a k := by
    simp only [cmpFn, map_mul, hM, div_zpow, Finset.prod_div_distrib]
    have n1 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
    have n2 : (∏ k, y ⟨k, c' k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc' k)
    have n3 : (∏ k, y ⟨bk k, bx k (c₀ k)⟩ ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyv k)
    have e3 : ∀ c₁ : (k : K₀) → J₀ k, (∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k) = ∏ k, y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k :=
      fun _ => rfl
    rw [e3, e3]
    by_cases he : e = 0
    · simp [he]
    · field_simp
  have hu2 := CxVal.unique hu' (key ▸ CxVal.mul (CxVal.mul hu e2) e1)
  have w1 : (∏ k, w ⟨k, c k⟩ ^ a k) = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c' k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hr' k, mul_zpow]
  have w2 : (∏ k, w (blkV bk bx ⟨k, c₀' k⟩) ^ a₀ k) =
      (∏ k, q k ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    show w ⟨bk k, bx k (c₀' k)⟩ ^ a₀ k = _
    rw [hq' k, mul_zpow]
    rfl
  have n4 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have n5 : (∏ k, q k ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hq0 k)
  simp only [cmpVal]
  rw [w1, w2, hu2]
  field_simp

end Val

section Points

open GroundTheory.Heights₂.Heights.LowerBoundFree (IsValueAt)

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀}
  {y : (Σ k, J k) → Ω} {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀}
  {w : (Σ k, J k) → ℂ}

theorem isCmp_unique (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hm : w ∈ mcPts (mCoordIdeal y)) {t t' : ℂ}
    (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) (h' : IsCmp i y₀ y bk bx a a₀ e e₀ w t') : t = t' := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  obtain ⟨c, c₀, u, h1, h2, -, hv, rfl⟩ := h
  obtain ⟨c', c₀', u', h1', h2', -, hv', rfl⟩ := h'
  exact cmpVal_eq hy hz hw h1 h1' h2 h2' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv)
    ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv')

theorem IsCmp.ne_zero {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) : t ≠ 0 := by
  obtain ⟨c, c₀, u, h1, h2, hu, -, rfl⟩ := h
  exact cmpVal_ne_zero h1 h2 hu

theorem IsCmp.smul (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hm : w ∈ mcPts (mCoordIdeal y)) {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) {s : K → ℂ}
    (hs : ∀ k, s k ≠ 0) :
    (fun p => s p.1 * w p) ∈ mcPts (mCoordIdeal y) ∧
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => s p.1 * w p)
      ((∏ k, s k ^ a k) / (∏ k, s (bk k) ^ a₀ k) * t) := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  have hw' : CoordsAt ξ y z (fun p => s p.1 * w p) := coordsAt_orbit hw ⟨s, hs, rfl⟩
  refine ⟨(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT _).2 ⟨z, hz, hw'⟩, ?_⟩
  obtain ⟨c, c₀, u, h1, h2, hu, hv, rfl⟩ := h
  refine ⟨c, c₀, u, fun k => mul_ne_zero (hs _) (h1 k), fun k => mul_ne_zero (hs _) (h2 k), hu,
    (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z _ hz hw' _ _).1 ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv), ?_⟩
  have n1 : (∏ k, s (bk k) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs _)
  have n2 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have e1 : (∏ k, (s (blkV bk bx ⟨k, c₀ k⟩).1 * w (blkV bk bx ⟨k, c₀ k⟩)) ^ a₀ k) =
      (∏ k, s (bk k) ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  have e2 : (∏ k, (s k * w ⟨k, c k⟩) ^ a k) = (∏ k, s k ^ a k) * ∏ k, w ⟨k, c k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  simp only [cmpVal]
  rw [e1, e2]
  field_simp

theorem eval_conj {σ : Type} (g : MvPolynomial σ ℤ) (w : σ → ℂ) :
    eval (fun p => starRingEnd ℂ (w p)) (map (Int.castRingHom ℂ) g) =
      starRingEnd ℂ (eval w (map (Int.castRingHom ℂ) g)) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, eval_X]

theorem conj_mem_mcPts (hm : w ∈ mcPts (mCoordIdeal y)) :
    (fun p => starRingEnd ℂ (w p)) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := hm.1 k
    exact ⟨x, by simpa using hx⟩
  · rw [eval_conj, hm.2 f hf, map_zero]

theorem IsCmp.conj {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) :
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => starRingEnd ℂ (w p)) (starRingEnd ℂ t) := by
  obtain ⟨c, c₀, u, h1, h2, hu, ⟨d, g, h, hg, hh, hy0, heq, hz0, rfl⟩, rfl⟩ := h
  refine ⟨c, c₀, _, fun k => by simpa using h1 k, fun k => by simpa using h2 k, ?_,
    ⟨d, g, h, hg, hh, hy0, heq, ?_, rfl⟩, ?_⟩
  · rw [eval_conj, eval_conj, ← map_div₀]
    simpa using hu
  · rw [eval_conj]
    simpa using hz0
  · simp only [cmpVal, map_div₀, map_mul, map_prod, map_zpow₀, eval_conj]

end Points

theorem exists_isRatio : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  intro X Ω Ω₀ _ _ ξ i K₀ K _ _ J₀ J _ _ y₀ y bk bx a a₀ e e₀ hT hall hbk hy hU
  classical
  have hval : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
      ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u ∧
        IsCmp i y₀ y bk bx a a₀ e e₀ w (cmpVal bk bx a a₀ w c c₀ u) := by
    intro z w hw c c₀ h1 h2
    obtain ⟨u, hu, hv⟩ := hU z w hw c c₀ h1 h2
    exact ⟨u, hu, hv, c, c₀, u, h1, h2, hu,
      (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w (hall _) hw _ _).1 hv, rfl⟩
  have hex : ∀ w ∈ mcPts (mCoordIdeal y), ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := by
    intro w hm
    obtain ⟨z, -, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
    choose c hc using hw.1
    choose c₀ hc₀ using restr_ne (isBlockMap_blkV bx hbk) hm.1
    obtain ⟨u, -, -, h⟩ := hval z w hw c c₀ (fun k => (hc k).ne_zero) hc₀
    exact ⟨_, h⟩
  let ψ : ((Σ k, J k) → ℂ) → ℂ := fun w =>
    if h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t then h.choose else 1
  have hψ : ∀ w ∈ mcPts (mCoordIdeal y), ∀ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t → ψ w = t := by
    intro w hm t ht
    have h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := ⟨t, ht⟩
    simp only [ψ, dif_pos h]
    exact isCmp_unique hT hy hm h.choose_spec ht
  refine ⟨fun w => ‖ψ w‖, fun w hm => ?_, fun w hm => ?_, fun w hm s hs => ?_, fun w hm => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hex w hm
    simpa [hψ w hm t ht] using ht.ne_zero
  · obtain ⟨t, ht⟩ := hex w hm
    show ‖ψ _‖ = ‖ψ w‖
    rw [hψ w hm t ht, hψ _ (conj_mem_mcPts hm) _ ht.conj, Complex.norm_conj]
  · obtain ⟨t, ht⟩ := hex w hm
    obtain ⟨hm', ht'⟩ := ht.smul hT hm hs
    show ‖ψ _‖ = _ * ‖ψ w‖
    have n : ∀ k, ‖s k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hs k)
    rw [hψ w hm t ht, hψ _ hm' _ ht', norm_mul, norm_div, norm_prod, norm_prod]
    congr 1
    simp only [norm_zpow, Pi.sub_apply, zpow_sub₀ (n _), Finset.prod_div_distrib]
    rw [prod_comp_zpow hbk (fun k => ‖s k‖) a₀]
  · obtain ⟨t, c, c₀, u, h1, h2, -, ⟨d, g, h, hg, hh, hy0, heq, hz0, -⟩, -⟩ := hex w hm
    let G : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) g)
    let H : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) h)
    have aG : AnalyticOnNhd ℂ G Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have aH : AnalyticOnNhd ℂ H Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have cH : Continuous H := MvPolynomial.continuous_eval _
    let V : Set ((Σ k, J k) → ℂ) := {x | H x ≠ 0} ∩ ((⋂ k, {x | x ⟨k, c k⟩ ≠ 0}) ∩
      ⋂ k, {x | x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0})
    have oV : IsOpen V := by
      refine (isOpen_ne_fun cH continuous_const).inter ((isOpen_iInter_of_finite fun k => ?_).inter
        (isOpen_iInter_of_finite fun k => ?_))
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
    have mV : ∀ x ∈ V, H x ≠ 0 ∧ (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := by
      intro x hx
      exact ⟨hx.1, fun k => Set.mem_iInter.1 hx.2.1 k, fun k => Set.mem_iInter.1 hx.2.2 k⟩
    refine ⟨V, fun x => cmpVal bk bx a a₀ x c c₀ (G x / H x), oV, ?_, ?_, ?_⟩
    · exact ⟨hz0, Set.mem_iInter.2 h1, Set.mem_iInter.2 h2⟩
    · intro x hx
      obtain ⟨x1, x2, x3⟩ := mV x hx
      have pr1 : ∀ p : Σ k, J k, AnalyticAt ℂ (fun x : (Σ k, J k) → ℂ => x p) x := fun p =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, J k => ℂ) p).analyticAt x
      refine ((((aG x (Set.mem_univ _)).fun_div (aH x (Set.mem_univ _)) x1).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => ?_)).fun_div
        (Finset.analyticAt_fun_prod _ fun k _ => ?_) ?_)
      · exact (pr1 _).zpow (x2 k)
      · exact (pr1 _).zpow (x3 k)
      · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (x3 k)
    · rintro x ⟨hx, hxm⟩
      obtain ⟨x1, x2, x3⟩ := mV x hx
      obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT x).1 hxm
      have hv : GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) x (G x / H x) :=
        ⟨d, g, h, hg, hh, hy0, heq, x1, rfl⟩
      obtain ⟨u, hu, hu', hc⟩ := hval z x hw c c₀ x2 x3
      have e1 : u = G x / H x :=
        CxVal.unique hu' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z x hz hw _ _).2 hv)
      rw [e1] at hc hu
      exact ⟨hc.ne_zero, by show ‖ψ x‖ = _; rw [hψ x hxm _ hc]⟩
  · intro z w hw c c₀ h1 h2
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).2 ⟨z, hall _, hw⟩
    obtain ⟨u, hu, hv, hc⟩ := hval z w hw c c₀ h1 h2
    refine ⟨u, hu, hv, ?_⟩
    have n : (∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (h2 k))
    show ‖ψ w‖ * _ = _
    rw [hψ w hm _ hc]
    simp only [cmpVal, norm_div, norm_mul, norm_prod, norm_zpow]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Chg.Ratio
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_reindexed_coords : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

theorem isHodgeLine_pull_tensor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T
    hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg
  haveI := hcz
  subst hA
  have hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h) := 𝔐₀.all _
  have hw₀ := hCoord z w hw
  have hI₀ := hInt z hI

  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1)
    (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, -, hn₀⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀
  have hgr₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩

  have ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩ := Subtype.ext (by
    show h (z _) = (z ≫ h) _
    exact (Scheme.Hom.comp_apply z h _).symm)
  have hgen := hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)
  obtain ⟨ν₁, -, hn₁⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen
  have hit : i t₀ ≠ 0 := hgen.1
  obtain ⟨u', -, hu', e'⟩ := (hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)
  have hu1 : u' = 1 := CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))
  obtain ⟨u₁, hu₁0, hu₁, eν⟩ := (hn₁ _ _).1 hg
  rw [hu1, norm_one, _root_.one_mul] at e'
  subst e'

  have hsec := hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀
  choose c₀ hc₀ using hw₀.1
  choose c hc using hw.1
  have hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hc₀ k).ne_zero
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨u₀, hu₀, en₀⟩ := hsec.2.2 c₀ hc₀'
  obtain ⟨u, -, hu, eT⟩ := hR z w hw c c₀ hc' hc₀'
  have ha : ((pullHerm hv A₀).tensor T).a = a := by
    show pullDeg bk A₀.a + T.a = a
    rw [hT]
    abel
  have hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1
  have hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0 :=
    (map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)
  refine (secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩
  · rw [ha]
    convert CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1
    rw [map_div₀, map_zpow₀, div_zpow]
    generalize i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) * e = n
    have hz : i t₀ ^ rootSgn D r ≠ 0 := zpow_ne_zero _ hit
    field_simp
  · rw [ha, eν]
    show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _
    rw [mul_zpow, norm_mul, norm_mul, norm_zpow]
    linear_combination (‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fifth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_coord_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | exact GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem root_model_on_cover : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), o.Fl.deg = 1 → Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift → Function.Bijective o.Re.π → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i → 𝔐.f = h ≫ o.𝔐.f → 𝔐.cst = i.comp o.𝔐.cst → (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) → (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) → Fl.RootLines xdeg e → 𝔐.OmVB → SmoothGenericFibreM y → ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧ o'.𝔐.R = 𝔐.R ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  intro hG E _ _ _ H D l Xo c Y Sys Fx R o S Ω _ _ K _ J _ y bk bx i 𝔐 h Fl xdeg e hdeg1 hemb hbij hbk hy hd hf hcst
    hfl hfin hlines hom hsm
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hv := isBlockMap_blkV bx hbk
  haveI : Nonempty K := ⟨bk o.k₀⟩
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl hβ
  have harith' : IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) := harith
  obtain ⟨R'⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω y _ harith' hsm
  have hP₀ : ¬ (⊤ : Ideal (MRing R.ι)) ≤ mCoordIdeal R.y := fun h' =>
    R.arith.2.1.1.ne_top (top_le_iff.1 h')
  have hle : mCoordIdeal R.y ≤ imageZ (blkV bk bx) (mCoordIdeal y) := mCoordIdeal_le_imageZ i bx hy
  let R₀ : AnLogRes (mCoordIdeal R.y) ⊤ (Top.dimFl (CMType H) (D.p + D.q)) := withTop o.Re.R hP₀ hemb
  obtain ⟨hh, hholo, horb⟩ := GlobalTheory.T.log_resolution_functorial_holomorphic R.K R.ι K J bk (blkV bk bx) (mCoordIdeal R.y) (mCoordIdeal y) ⊤ _ _ R₀ R' hv hle
  have hdpos : 0 < Fl.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, -⟩ := Fl.generic
    exact h0
  obtain ⟨br₀, hdeg₀⟩ := GlobalTheory.T.log_resolution_reindexed R.K K R.ι J R.Ω Ω R.y y bk bx i _ Fl.deg R₀ R' hh hbk hy R.arith harith'
    R.birational hbir hholo horb hfin hdpos
  obtain ⟨hholoπ, hdeg⟩ := GlobalTheory.T.holomorphic_degree_composition _ Fl.deg Sys.X o.Re.R.X R'.X Sys.A o.Re.R.A R'.A o.Re.π hh br₀ o.Re.holo hbij
    hholo hdeg₀
  obtain ⟨hreg, hrefl, hval⟩ := GlobalTheory.T.dominating_regular_push 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i hd 𝔐.tie.gen
  have hval' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : R.Ω) (r : ℂ), ValAt o.𝔐.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r :=
    fun z a r => hval z a r (𝔐.all _)
  have hco := GlobalTheory.T.dominating_coords_reindexed 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i R.K K R.ι J R.y y bk bx hd o.𝔐.tie 𝔐.all hy hval'
  have hcov : IsCovOf o.𝔐 𝔐 i h := ⟨hd, hf, hcst⟩
  obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := GlobalTheory.T.hodge_comp_descent_first E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl hβ hcov hfl
  have hgen : GenPull o.Fl Fl i hd :=
    GlobalTheory.T.hodge_comp_descent_second E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j hreg hj1 hj2 hj3 hj4
  have hnorm : NormPull o.Fl Fl i h :=
    GlobalTheory.T.hodge_comp_descent_third E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j inferInstance hreg hj1 hj2 hj3 hj4 hj5
  have hab := mem_abLocus_iff o.𝔐 𝔐 h hf
  have hT : ∀ r : RootIx D, ∃ T : HermLine J, T.a = xdeg r - pullDeg bk (R.xdeg r) ∧ IsSmoothHerm T ∧
      IsConjInvariantH T ∧ IsFlatOn R' T ∧ IsRatio 𝔐.ξ y R.y bk bx i (xdeg r) (R.xdeg r) (e r) (o.e r) T.h := by
    intro r
    have hu := GlobalTheory.T.hodge_comp_descent_fourth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx (xdeg r) (R.xdeg r)
      (e r) (o.e r) r hβ inferInstance hy hgen (o.lines r) (hlines r) hrefl hreg hco
    obtain ⟨φ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.degree_reindexed_coords 𝔐.X Ω R.Ω 𝔐.ξ i R.K K R.ι J R.y y bk bx (xdeg r) (R.xdeg r) (e r) (o.e r)
      𝔐.tie 𝔐.all hbk hy hu
    obtain ⟨T, t1, t2, t3, t4, t5⟩ := GlobalTheory.T.positive_homogeneous_potential K J _ _ R' _ φ h1 h2 h3 h4
    refine ⟨T, t1, t2, t3, t5, fun z w hw c c₀ hc hc₀ => ?_⟩
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).2 ⟨z, 𝔐.all _, hw⟩
    rw [t4 w hm]
    exact h5 z w hw c c₀ hc hc₀
  choose T hTa hTs hTc hTf hTr using hT
  have hmem : ∀ z ∈ mcPts (mCoordIdeal y), (fun p => z (blkV bk bx p)) ∈ mcPts (mCoordIdeal R.y) :=
    fun z hz => mem_mcPts_restr hv hle hz
  have hlift : ∀ x, ∀ k, ∃ a, R'.lift x x ⟨k, a⟩ ≠ 0 := fun x => (R'.mem x x (R'.mem_U x)).1
  have hlift₀ : ∀ x k, ∃ a, R'.lift x x (blkV bk bx ⟨k, a⟩) ≠ 0 := fun x => restr_ne hv (hlift x)
  have horb' : ∀ x, SameOrbit (o.Re.R.lift (hh x) (hh x)) (fun p => R'.lift x x (blkV bk bx p)) := horb
  let RM : Top.RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := J, Ω := Ω, y := y, arith := harith', birational := hbir, xdeg := xdeg
      x := fun t r => (pullHerm hv (R.x t r)).tensor (T r)
      x_deg := fun t r => by
        show pullDeg bk (R.x t r).a + (T r).a = xdeg r
        rw [R.x_deg, hTa]
        abel
      x_smooth := fun t r => isSmoothHerm_tensor (isSmoothHerm_pull hv (R.x_smooth t r)) (hTs r)
      x_conj := fun t r => isConj_tensor (isConj_pull hv (R.x_conj t r)) (hTc r)
      kA := R.kA, kA_pos := R.kA_pos
      A := pullHerm hv R.A
      A_smooth := isSmoothHerm_pull hv R.A_smooth
      A_conj := isConj_pull hv R.A_conj
      δ := Module.finrank ℚ c.F * Fl.deg
      δ_pos := Nat.mul_pos (Nat.pos_of_ne_zero fun h0 => by
        have h1 := R.δ_pos
        rw [o.δ_eq, h0, zero_mul] at h1
        exact lt_irrefl _ h1) hdpos }
  let Re' : PB.Realis Sys (mCoordIdeal y) :=
    { arith := harith', J := ⊤, R := R', π := o.Re.π ∘ hh, holo := hholoπ, deg := Fl.deg, deg_pos := hdpos
      br := o.Re.π '' br₀, degree := hdeg
      ref := fun a => (pullHerm hv (o.Re.ref a)).tensor (corr T a)
      ref_smooth := fun a => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.ref_smooth a)) (isSmoothHerm_corr hTs a)
      ref_pot := fun a => GlobalTheory.T.log_resolution_potential_pullback R.K K R.ι J bk (blkV bk bx) _ _ _ _ _ o.Re.R R' Sys.X Sys.A (Sys.th a) (o.Re.ref a)
        (corr T a) o.Re.π o.Re.holo hh hv hholoπ.1 hholo horb' (o.Re.ref_pot a) (GlobalTheory.T.flat_on_log_resolution_corr K J _ _ _ R' _ _ T hTf a)
      line := fun a t => (pullHerm hv (o.Re.line a t)).tensor (corr T a)
      line_deg := fun a t => by
        show pullDeg bk (o.Re.line a t).a + (corr T a).a = pullDeg bk (o.Re.ref a).a + (corr T a).a
        rw [o.Re.line_deg]
      line_smooth := fun a t h0 h1 => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.line_smooth a t h0 h1))
        (isSmoothHerm_corr hTs a)
      line_eq := fun a t h0 h1 x => by
        have e1 := o.Re.line_eq a t h0 h1 (hh x)
        have e2 := log_sub_orbit (o.Re.line_deg a t) (horb' x) (hlift₀ x)
        rw [log_tensor_pull hv _ _ (hlift x), log_tensor_pull hv _ _ (hlift x)]
        show _ = _ + Sys.phT a t (o.Re.π (hh x))
        linarith }
  have hsing : ∀ r, ((pullHerm hv (o.sing r)).tensor (T r)).a = xdeg r := fun r => by
    show pullDeg bk (o.sing r).a + (T r).a = xdeg r
    rw [o.sing_deg, hTa]
    abel
  have hInt : ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z ↔ o.𝔐.Interior (z ≫ h) := fun z => hab (centre z)
  let o' : RootOrigin Y S RM Fx :=
    { 𝔐 := 𝔐, Fl := Fl, g := i.comp o.g
      g_over := by
        have hd' : 𝔐.ξ ≫ h = spMap i ≫ o.𝔐.ξ := hd
        rw [hf, ← Category.assoc, hd', Category.assoc, o.g_over, spMap_comp', Category.assoc]
      g_flag := fun s a => by
        rw [hfl s a, o.g_flag s a, dualMap_comp', spMap_comp', Category.assoc]
      g_deg := by
        have e1 := finrank_comp' o.g i
        have e2 := o.g_deg
        rw [hdeg1] at e2
        rw [e2, _root_.one_mul] at e1
        exact e1.trans hfin
      g_const := fun a ha => by
        obtain ⟨b, hb⟩ := o.g_const a ha
        exact ⟨b, by rw [hcst]; simp [hb]⟩
      δ_eq := rfl
      e := e, lines := hlines
      sing := fun r => (pullHerm hv (o.sing r)).tensor (T r)
      sing_deg := hsing
      hodge := fun r => GlobalTheory.T.hodge_comp_descent_fifth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx hv r (xdeg r)
        (R.xdeg r) (e r) (o.e r) (o.sing r) (T r) hβ inferInstance hy hgen hnorm hval' hco (fun z => (hInt z).1) (hlines r).1
        (o.sing_deg r) (hTa r) (hTr r) (o.hodge r)
      k₀ := bk o.k₀
      ix := o.ix.trans (bx o.k₀)
      y_eq := fun a => by
        show y ⟨bk o.k₀, bx o.k₀ (o.ix a)⟩ = i (o.g (Fx.yf a))
        rw [hy, o.y_eq]
      kA_eq := o.kA_eq
      A_deg := by
        constructor
        · show pullDeg bk R.A.a (bk o.k₀) = 1
          rw [pullDeg, hbk.extend_apply]
          exact o.A_deg.1
        · intro k hk
          show pullDeg bk R.A.a k = 0
          by_cases h' : ∃ a, bk a = k
          · obtain ⟨a, rfl⟩ := h'
            rw [pullDeg, hbk.extend_apply]
            exact o.A_deg.2 a fun e' => hk (by rw [e'])
          · rw [pullDeg, Function.extend_apply' _ _ _ h']
            rfl
      A_h := fun z hz => o.A_h _ (hmem z hz)
      eff := GlobalTheory.T.root_origin_coord_field E H D l Xo c _ _ Y Sys Fx R ∅ S o Ω K J y bk bx 𝔐 i h hd Fl xdeg e hy hgen hlines hrefl hreg hab
      Re := Re', Re_deg := rfl
      π_pt := fun x => by
        obtain ⟨a₀, ha₀⟩ := o.π_pt (hh x)
        obtain ⟨c', hc', hw⟩ := horb' x
        refine ⟨(c' o.k₀)⁻¹ * a₀, funext fun i' => ?_⟩
        have e1 := congrFun ha₀ i'
        simp only [Pi.smul_apply, smul_eq_mul] at e1
        rw [hw] at e1
        have e2 : c' o.k₀ * R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = a₀ * Fx.pt (o.Re.π (hh x)) i' := e1
        show R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = (c' o.k₀)⁻¹ * a₀ * Fx.pt (o.Re.π (hh x)) i'
        rw [_root_.mul_assoc, ← e2, inv_mul_cancel_left₀ (hc' o.k₀)]
      interior := fun x z hz => by
        have h1 : CoordsAt o.𝔐.ξ R.y (z ≫ h) (o.Re.R.lift (hh x) (hh x)) := coordsAt_orbit (hco z _ hz) (horb' x)
        exact (hInt z).trans (o.interior (hh x) (z ≫ h) h1)
      fund_deg := fun τ a => by
        show pullDeg bk (o.Re.ref (some (τ, a))).a + (stepLine (fun k => T (τ, k)) a).a = -∑ k ∈ Finset.Iic a, xdeg (τ, k)
        rw [o.fund_deg, pullDeg_neg_sum hbk]
        funext k
        simp only [stepLine, hTa, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
        show _ = -∑ k' ∈ Finset.Iic a, xdeg (τ, k') k
        ring
      fund_sing := fun τ a x hx => by
        have e1 := o.fund_sing τ a (hh x) hx
        have hab' : (o.Re.ref (some (τ, a))).a = -∑ k ∈ Finset.Iic a, (o.sing (τ, k)).a := by
          rw [o.fund_deg]
          simp only [o.sing_deg]
        have e2 := log_sum_orbit (Finset.Iic a) hab' (horb' x) (hlift₀ x)
        show Real.log (((pullHerm hv (o.Re.ref (some (τ, a)))).tensor (stepLine (fun k => T (τ, k)) a)).h (R'.lift x x)) +
            Sys.ph (some (τ, a)) (o.Re.π (hh x)) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (o.sing (τ, k))).tensor (T (τ, k))).h (R'.lift x x))
        rw [log_tensor_pull hv _ _ (hlift x), log_stepLine _ _ (hlift x)]
        simp only [log_tensor_pull hv _ _ (hlift x), Finset.sum_add_distrib]
        linarith
      fund_reg := fun τ a t h0 h1 z hz => by
        have hz' : z ∈ mcPts (mCoordIdeal y) := hz
        have e1 := o.fund_reg τ a t h0 h1 _ (hmem z hz')
        show Real.log (((pullHerm hv (o.Re.line (some (τ, a)) t)).tensor (stepLine (fun k => T (τ, k)) a)).h z) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (R.x t (τ, k))).tensor (T (τ, k))).h z)
        rw [log_tensor_pull hv _ _ hz'.1, log_stepLine _ _ hz'.1]
        simp only [log_tensor_pull hv _ _ hz'.1, Finset.sum_add_distrib]
        linarith
      ref_none := by
        refine ⟨?_, fun z hz => ?_⟩
        · show pullDeg bk (o.Re.ref none).a + 0 = pullDeg bk R.A.a
          rw [o.ref_none.1, add_zero]
        · show (o.Re.ref none).h (fun p => z (blkV bk bx p)) * 1 = R.A.h fun p => z (blkV bk bx p)
          rw [_root_.mul_one]
          exact o.ref_none.2 _ (hmem z hz) }
  exact ⟨RM, o', hom, rfl, rfl, inferInstance, hsm⟩

end GlobalTheory.CompanionTheory.Ar
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_coords_over_field : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), o.Fl.deg = 1 → Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift → Function.Bijective o.Re.π → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i → 𝔐.f = h ≫ o.𝔐.f → 𝔐.cst = i.comp o.𝔐.cst → (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) → (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) → Fl.RootLines xdeg e → 𝔐.OmVB → SmoothGenericFibreM y → ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧ o'.𝔐.R = 𝔐.R ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.root_model_on_cover
end
