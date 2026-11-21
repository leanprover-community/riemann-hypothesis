import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmetic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThird
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventh
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartNinth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetric
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimension
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_adapted_atlas_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | exact GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection <;> assumption)
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem dim_eq_of_holo_inverse {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas a X) (B : FinHolAtlas b Y) (f : X → Y) (g : Y → X)
    (hf : HoloMap A B f) (hg : HoloMap B A g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) :
    a = b := by
  obtain ⟨j, hj⟩ := A.cover x
  obtain ⟨k, hk⟩ := B.cover (f x)
  have hu_t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hw_t : B.chart k (f x) ∈ (B.chart k).target := (B.chart k).map_source hk
  have hsu : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hsw : (B.chart k).symm (B.chart k (f x)) = f x := (B.chart k).left_inv hk
  let F : (Fin a → ℂ) → (Fin b → ℂ) := B.chart k ∘ f ∘ (A.chart j).symm
  let G : (Fin b → ℂ) → (Fin a → ℂ) := A.chart j ∘ g ∘ (B.chart k).symm
  have hFu : F (A.chart j x) = B.chart k (f x) := by
    show B.chart k (f ((A.chart j).symm (A.chart j x))) = _
    rw [hsu]
  have hGw : G (B.chart k (f x)) = A.chart j x := by
    show A.chart j (g ((B.chart k).symm (B.chart k (f x)))) = _
    rw [hsw, hgf]
  have dF : DifferentiableAt ℂ F (A.chart j x) :=
    (hf.2 j k _ ⟨hu_t, by
      show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
      rw [hsu]; exact hk⟩).differentiableAt
  have dG : DifferentiableAt ℂ G (B.chart k (f x)) :=
    (hg.2 k j _ ⟨hw_t, by
      show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
      rw [hsw, hgf]; exact hj⟩).differentiableAt
  have e1 : G ∘ F =ᶠ[𝓝 (A.chart j x)] id := by
    have c : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
      hf.1.continuousAt.comp ((A.chart j).continuousAt_symm hu_t)
    have hs : ∀ᶠ v in 𝓝 (A.chart j x), (f ∘ (A.chart j).symm) v ∈ (B.chart k).source :=
      c.eventually ((B.chart k).open_source.mem_nhds (by
        show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
        rw [hsu]; exact hk))
    filter_upwards [hs, (A.chart j).open_target.mem_nhds hu_t] with v h1 h2
    have h1' : f ((A.chart j).symm v) ∈ (B.chart k).source := h1
    show A.chart j (g ((B.chart k).symm (B.chart k (f ((A.chart j).symm v))))) = v
    rw [(B.chart k).left_inv h1', hgf, (A.chart j).right_inv h2]
  have e2 : F ∘ G =ᶠ[𝓝 (B.chart k (f x))] id := by
    have c : ContinuousAt (g ∘ (B.chart k).symm) (B.chart k (f x)) :=
      hg.1.continuousAt.comp ((B.chart k).continuousAt_symm hw_t)
    have hs : ∀ᶠ v in 𝓝 (B.chart k (f x)), (g ∘ (B.chart k).symm) v ∈ (A.chart j).source :=
      c.eventually ((A.chart j).open_source.mem_nhds (by
        show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
        rw [hsw, hgf]; exact hj))
    filter_upwards [hs, (B.chart k).open_target.mem_nhds hw_t] with v h1 h2
    have h1' : g ((B.chart k).symm v) ∈ (A.chart j).source := h1
    show B.chart k (f ((A.chart j).symm (A.chart j (g ((B.chart k).symm v))))) = v
    rw [(A.chart j).left_inv h1', hfg, (B.chart k).right_inv h2]
  have d1 : (fderiv ℂ G (B.chart k (f x))).comp (fderiv ℂ F (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    have dG' : DifferentiableAt ℂ G (F (A.chart j x)) := by rw [hFu]; exact dG
    have h := fderiv_comp (A.chart j x) dG' dF
    rw [e1.fderiv_eq, fderiv_id, hFu] at h
    exact h.symm
  have d2 : (fderiv ℂ F (A.chart j x)).comp (fderiv ℂ G (B.chart k (f x))) = ContinuousLinearMap.id ℂ _ := by
    have dF' : DifferentiableAt ℂ F (G (B.chart k (f x))) := by rw [hGw]; exact dF
    have h := fderiv_comp (B.chart k (f x)) dF' dG
    rw [e2.fderiv_eq, fderiv_id, hGw] at h
    exact h.symm
  let E : (Fin a → ℂ) ≃ₗ[ℂ] (Fin b → ℂ) := LinearEquiv.ofLinearMap
    (fderiv ℂ F (A.chart j x) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    (fderiv ℂ G (B.chart k (f x)) : (Fin b → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (LinearMap.ext fun v => congrArg (fun L : (Fin b → ℂ) →L[ℂ] (Fin b → ℂ) => L v) d2)
    (LinearMap.ext fun v => congrArg (fun L : (Fin a → ℂ) →L[ℂ] (Fin a → ℂ) => L v) d1)
  simpa using E.finrank_eq

theorem dim_eq_of_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {a b : ℕ}
    (R : AnLogRes P ⊤ a) (hJ : J = ⊤) (R' : AnLogRes P J b) (x : R'.X) : a = b := by
  subst hJ
  have hP : P ≤ imageZ id P := fun f hf => by
    show rename id f ∈ P
    rwa [rename_id_apply]
  obtain ⟨h, hh, ho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ a b R R' isBlockMap_id hP
  obtain ⟨g, hg, go⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ b a R' R isBlockMap_id hP
  have hemp : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun z hz => by
    have := hz.2 1 trivial
    simp at this
  have hgh : ∀ x, g (h x) = x := fun x => R'.inj _ _ (hemp _) (orbit_trans (go (h x)) (ho x))
  have hhg : ∀ x, h (g x) = x := fun x => R.inj _ _ (hemp _) (orbit_trans (ho (g x)) (go x))
  exact dim_eq_of_holo_inverse R.A R'.A g h hg hh hhg hgh (h x)

theorem flagAn_dim : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hk : ∀ k, k ∈ Set.range (id : K → K) ↔
      ((∀ p, M.blk p ≠ some k) ∨ ∃ p, (fun _ : Ψ × Fin N => True) p ∧ M.blk p = some k) := fun k =>
    ⟨fun _ => by
      by_cases h : ∀ p, M.blk p ≠ some k
      · exact Or.inl h
      · obtain ⟨p, hp⟩ := not_forall.1 h
        exact Or.inr ⟨p, trivial, not_not.1 hp⟩, fun _ => ⟨k, rfl⟩⟩
  obtain ⟨e, R, he, -⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n _ BM.Rb rfl (fun _ => True) K ι id id isBlockMap_id hk
  have R2 : AnLogRes (mCoordIdeal y) ⊤ e := R
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts FA.Re.arith FA.Re.R.nondeg
  obtain ⟨x, -⟩ := FA.Re.R.surj z hz hJ
  rw [← he fun _ => trivial]
  exact (dim_eq_of_res R2 FA.J_top FA.Re.R x).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_dimension_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

abbrev LPt : Type := (Σ _ : Unit, Fin 2) → ℂ

def lineφ (w : Fin 1 → ℂ) : LPt := fun q => ![1, w 0] q.2

def lineρ (z : LPt) : Fin 1 → ℂ := fun _ => z ⟨(), 1⟩ / z ⟨(), 0⟩

@[simp] theorem lineφ_zero (w : Fin 1 → ℂ) : lineφ w ⟨(), 0⟩ = 1 := rfl

@[simp] theorem lineφ_one (w : Fin 1 → ℂ) : lineφ w ⟨(), 1⟩ = w 0 := rfl

theorem lineφ_mem (w : Fin 1 → ℂ) :
    lineφ w ∈ mcPts (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) := by
  refine ⟨fun k => ⟨0, by cases k; simp⟩, fun f hf => ?_⟩
  have : f = 0 := by simpa using hf
  simp [this]

theorem lineφ_analytic (q : Σ _ : Unit, Fin 2) :
    AnalyticOnNhd ℂ (fun w : Fin 1 → ℂ => lineφ w q) Set.univ := by
  obtain ⟨⟨⟩, i⟩ := q
  fin_cases i
  · exact analyticOnNhd_const
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticOnNhd _

theorem lineρ_lineφ (w : Fin 1 → ℂ) : lineρ (lineφ w) = w := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [lineρ]

theorem lineρ_affCoord (p : (k : Unit) → Fin 2) (w : Fin 1 → ℂ) :
    lineρ (affCoord p (lineφ w)) = w := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hp : p () = 0 ∨ p () = 1 := by
    rcases h : p () with ⟨n, hn⟩
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hp with hp | hp
  · simp [lineρ, affCoord, hp]
  · by_cases h : w 0 = 0
    · simp [lineρ, affCoord, hp, h]
    · simp [lineρ, affCoord, hp, h]

theorem line_diff_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) (h : g x ≠ 0) :
    DifferentiableAt ℂ (fun y => f y / g y) x := by
  simp only [div_eq_mul_inv]
  exact hf.fun_mul ((differentiableAt_inv h).comp x hg)

theorem line_immersion (w : Fin 1 → ℂ) (p : (k : Unit) → Fin 2)
    (hw : ∀ k, lineφ w ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun w' => affCoord p (lineφ w')) w).ker = ⊥ := by
  have hφ : ∀ q, DifferentiableAt ℂ (fun w' : Fin 1 → ℂ => lineφ w' q) w := fun q =>
    ((lineφ_analytic q) w (Set.mem_univ _)).differentiableAt
  have hF : DifferentiableAt ℂ (fun w' => affCoord p (lineφ w')) w :=
    differentiableAt_pi.2 fun q => by
      show DifferentiableAt ℂ (fun w' => lineφ w' q / lineφ w' ⟨q.1, p q.1⟩) w
      exact line_diff_div (hφ q) (hφ ⟨q.1, p q.1⟩) (hw q.1)
  have h0 : affCoord p (lineφ w) ⟨(), 0⟩ ≠ 0 := by
    have hp : p () = 0 ∨ p () = 1 := by
      rcases h : p () with ⟨n, hn⟩
      interval_cases n
      · exact Or.inl rfl
      · exact Or.inr rfl
    have := hw ()
    rcases hp with hp | hp
    · simp [affCoord, hp]
    · rw [hp] at this
      simpa [affCoord, hp] using this
  have hG : DifferentiableAt ℂ lineρ (affCoord p (lineφ w)) :=
    differentiableAt_pi.2 fun _ => by
      exact line_diff_div (differentiableAt_apply (𝕜 := ℂ) (⟨(), 1⟩ : Σ _ : Unit, Fin 2) _)
        (differentiableAt_apply (𝕜 := ℂ) (⟨(), 0⟩ : Σ _ : Unit, Fin 2) _) h0
  have hcomp := hG.hasFDerivAt.comp w hF.hasFDerivAt
  have hid : (lineρ ∘ fun w' => affCoord p (lineφ w')) = id := by
    funext w'
    exact lineρ_affCoord p w'
  rw [hid] at hcomp
  have hEq := hcomp.unique (hasFDerivAt_id w)
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) => L a) hEq
  have h2 := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) => L b) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2]
  exact congrArg _ hab

def lineChart : OrbitChart (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) 1 where
  D := Set.univ
  isOpen_D := isOpen_univ
  φ := lineφ
  holo := lineφ_analytic
  mem w _ := lineφ_mem w
  O := {z | z ∈ mcPts (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) ∧ z ⟨(), 0⟩ ≠ 0}
  O_open := by
    refine ⟨{z | z ⟨(), 0⟩ ≠ 0}, isOpen_ne_fun (continuous_apply _) continuous_const, ?_⟩
    ext z
    exact and_comm
  O_orbit := by
    rintro z ⟨_, hz⟩ z' hz' ⟨c, hc, rfl⟩
    exact ⟨hz', mul_ne_zero (hc _) hz⟩
  ρ := lineρ
  ρ_cont := by
    refine continuousOn_pi.2 fun _ => ?_
    exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn fun z hz => hz.2
  ρ_orbit := by
    rintro z ⟨_, hz⟩ z' _ ⟨c, hc, rfl⟩
    funext i
    exact mul_div_mul_left _ _ (hc _)
  φ_mem_O w _ := ⟨lineφ_mem w, by simp⟩
  ρ_φ w _ := lineρ_lineφ w
  ρ_mem _ _ := Set.mem_univ _
  φ_ρ := by
    rintro z ⟨_, hz⟩
    refine ⟨fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero hz, ?_⟩
    funext q
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i
    · simp [hz]
    · simp [lineρ, div_eq_inv_mul]
  immersion w _ p hw := line_immersion w p hw

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holoMap_of_local_product_charts : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_dimension_index_equiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_from_orbit_charts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, ∀ z' ∈ mcPts (wP M τ a k₀ ca cb), SameOrbit z' z → z' ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε z' = wRho M Rb τ k₀ ca cb F kb r h ε z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_eighth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_ninth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, ∀ p : (o : Option K) → ι (o.getD k₀), (∀ o, wPhi M F bl h ε k₀ τ ca cb w ⟨o, p o⟩ ≠ 0) → (fderiv ℂ (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) w).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_arithmetic_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ z ∈ mcPts (wP M τ a k₀ ca cb), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ z ∈ wO M Rb τ a k₀ ca cb F kb V r h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main <;> assumption)
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_baseOf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (baseOf M k₀ z) (baseOf M k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k.1), fun k => hc _, rfl⟩

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (show (⟨k, m⟩ : Σ k, ι k).1 ≠ k₀ from e), if_neg e]

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem fibreSquare_atlas : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy hd
  have hA := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  obtain ⟨ε⟩ := GlobalTheory.T.flag_dimension_index_equiv Ψ N j n d M.j_le hd
  have hcov := GlobalTheory.T.flag_adjacent_arithmetic_height K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h →
      ∃ C : OrbitChart (wP M τ a k₀ ca cb) (d + 2), C.D = wD ε V ∧ C.φ = wPhi M F bl h ε k₀ τ ca cb ∧
        C.O = wO M Rb τ a k₀ ca cb F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.2.2.2.2.1.1
    have hh := GlobalTheory.T.flag_adjacent_chart_first K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hr := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ho := GlobalTheory.T.flag_adjacent_chart_fifth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hO := GlobalTheory.T.flag_adjacent_chart_sixth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
    have hb' := GlobalTheory.T.flag_adjacent_chart_seventh K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ht := GlobalTheory.T.flag_adjacent_chart_eighth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hi := GlobalTheory.T.flag_adjacent_chart_ninth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    exact ⟨{ D := wD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := wPhi M F bl h ε k₀ τ ca cb
             holo := hh
             mem := hm
             O := wO M Rb τ a k₀ ca cb F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := wRho M Rb τ k₀ ca cb F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := GlobalTheory.T.log_resolution_from_orbit_charts (Option K) (fun o => ι (o.getD k₀)) (wP M τ a k₀ ca cb) (d + 2) hA.1 hA.2.1.2.1
    (fun h => hA.2.1.1.ne_top (top_le_iff.mp h)) (fun z hz => by
      obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
      obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
      exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = wD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (baseOf M k₀ (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    refine ⟨(Rb.A.chart kb).symm (wB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := sameOrbit_baseOf M (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ψ.target = wD ε V → x ∈ ψ.source →
      SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x)) (R.lift x x) →
      pr x ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    have h1 : SameOrbit (bl (wB ε (ψ x))) (baseOf M k₀ (R.lift x x)) := by
      have := sameOrbit_baseOf M hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (wB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_mcPts_top _) h2
    have hwt : wB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨(Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  refine ⟨R, pr, ?_, hpr, fun x => ?_⟩
  · refine GlobalTheory.T.holoMap_of_local_product_charts (d + 2) n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    exact ⟨ψ, kb, fun i => ε (Sum.inl i), hC, hx, fun x' hx' => hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')⟩
  · obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hB := hc.2.2.2.2.2.2.2.1
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun i i' e => Sum.inl_injective (ε.injective e)⟩, ε (Sum.inr (Sum.inr ())), F,
      fun τ' => wH h ε τ', hx, hC, hc.2.2.2.2.2.2.1, fun i e => Sum.inl_ne_inr (ε.injective e), fun x' hx' =>
        hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx'), fun τ' r' s' => hT ▸ hE.1 τ' r' s', fun x' hx' => ?_⟩
    have hw : ψ x' ∈ wD ε V := hT ▸ ψ.map_source hx'
    obtain ⟨e1, e2, e3⟩ := hE.2 _ hw
    have h1 := sameOrbit_baseOf M (hs x' hx')
    rw [e2] at h1
    refine ⟨e1, ?_, fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')), sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')),
      sameOrbit_fstPt (hs x' hx'), sameOrbit_sndPt (hs x' hx'), e3⟩
    have h2 : mCoordIdeal (bl (wB ε (ψ x'))) = mCoordIdeal (basePart M.blk (fstPt k₀ (R.lift x' x'))) :=
      GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit h1
    exact h2 ▸ (hB.2.2.2.2 _ hw).2.2.1

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections <;> assumption)
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SysPull

theorem finite_bound {ι : Type} [Finite ι] (f : ι → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem finite_scale {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := finite_bound fun a => (f a)⁻¹
  by_cases he : Nonempty ι
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    exact ⟨M⁻¹, inv_pos.2 hM0, fun a => inv_le_of_inv_le₀ (hf a) (hM a)⟩
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem pullback_common : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  intro e e' σ _ S X' _ _ _ A' Θ' L' s' nb m W q hq hP pΘ' posΘ' pL' sec' snc' nrm hL hs
  have key : ∀ p : Fin 2 × σ, ∃ C' t' : ℝ,
      IsSingWeight A' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1) S.C₅ ∧
      IsRegFamily A' Θ' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1)
        (fun t => S.phT p.2 t ∘ q p.1) C' t' ∧
      IsRegFamilyC2 A' s' (S.ph p.2 ∘ q p.1) (fun t => S.phT p.2 t ∘ q p.1) := by
    rintro ⟨i, a⟩
    have snc_i : IsSNC A' (S.L.pullback (q i) (hq i).1) (fun x y => S.s (q i x) (q i y)) m W := by
      rw [hL i, hs i]
      exact snc'
    obtain ⟨C', t', h1, h2, h3⟩ := hP S.A A' (q i) (hq i) S.Θ S.L Θ' S.s S.m S.W m W S.potΘ S.posΘ pΘ' posΘ'
      S.potL S.sec S.snc S.norm_le snc_i (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
    rw [hL i, hs i] at h1 h2
    rw [hs i] at h3
    exact ⟨C', t', h1, h2, h3⟩
  choose C' t' h1 h2 h3 using key
  by_cases hσ : Nonempty σ
  · obtain ⟨a₀⟩ := hσ
    obtain ⟨D, hD⟩ := finite_bound fun p => |C' p|
    obtain ⟨T₀, hT₀, hT⟩ := finite_scale t' fun p => (h2 p).1
    have hS : 0 < S.t₀ := (S.reg a₀).1
    refine ⟨S.C₅, D, min (min T₀ S.t₀) (Real.exp (-1)),
      (min_le_left _ _).trans (min_le_right _ _), fun i a => ⟨h1 (i, a), ?_, h3 (i, a)⟩⟩
    exact (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e' X' A' Θ' L' s' nb m W pL' sec' snc' nrm pΘ' posΘ').2.1 _ _ _ _ _ _ _ (hD (i, a))
      (lt_min (lt_min hT₀ hS) (Real.exp_pos _)) ((min_le_left _ _).trans ((min_le_left _ _).trans (hT (i, a))))
      (min_le_right _ _) (h2 (i, a)) (h1 (i, a)).1
  · exact ⟨0, 0, S.t₀, le_rfl, fun _ a => absurd ⟨a⟩ hσ⟩

end GlobalTheory.CompanionTheory.Ar.PB.SysPull
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_map_pullback_energy : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem ansq_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  intro hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har
  have hdim := GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA
  obtain ⟨RW, pr, hpr, hbase, hch⟩ := GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim
  obtain ⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩ :=
    GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase
  have hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)),
      IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i)) := fun x => by
    obtain ⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩ := hch x
    exact ⟨ψ, kb, σ, h1, hx, h4⟩
  obtain ⟨pL, sL, nL, -⟩ := GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch'
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW
  have hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1 := fun i => by
    show FA.S.L.pullback (q i) (hq i).1 = _
    have e := FA.L_eq
    revert e
    generalize FA.S.L = LL
    intro e
    subst e
    exact pullback_pullback _ _ _ _ _ _ _ (hpq i)
  have hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y) := fun i => by
    funext x y
    show FA.S.s (q i x) (q i y) = _
    rw [FA.s_eq]
    show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _
    rw [hpq i]
  obtain ⟨C₅, C, t₀, ht₀, hmem⟩ := GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A
    (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_le (pr x)) hL hs'
  obtain ⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩ :=
    GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩
  obtain ⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩ :=
    GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj
  obtain ⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩ :=
    GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc
  let SW : AnSys (d + 2) (Option (Ψ × Fin N)) :=
    { X := RW.X
      A := RW.A
      Θ := potOf RW (fsHerm _ fun _ => 1)
      L := BM.L.pullback pr hpr.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := fun x => BM.norm_le (pr x)
      th := fun o => o.elim (((FA.S.comap some).th (τ, a)).pullback (q 1) (hq 1).1)
        fun p => ((FA.S.comap some).th p).pullback (q 0) (hq 0).1
      ph := fun o => o.elim ((FA.S.comap some).ph (τ, a) ∘ q 1) fun p => (FA.S.comap some).ph p ∘ q 0
      phT := fun o => o.elim (fun t => (FA.S.comap some).phT (τ, a) t ∘ q 1)
        fun p t => (FA.S.comap some).phT p t ∘ q 0
      C₅ := C₅
      C := C
      t₀ := t₀
      sing := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).1
        | some p => exact (hmem 0 p).1
      reg := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.1
        | some p => exact (hmem 0 p).2.1
      c2 := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.2
        | some p => exact (hmem 0 p).2.2 }
  have hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P :=
    fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩
  let Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a) :=
    { eps_a₀ := by simp [xiCoef]
      SW := SW
      q := q
      holo := hq
      bdry_eq := fun i => by
        ext x
        show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0
        rw [FA.s_eq]
        show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0
        rw [hpq i]
      t₀_le := ht₀
      th0 := fun p => hsame _ _
      th1 := hsame _ _
      ph0 := fun _ => rfl
      ph1 := rfl
      phase_some_eq_comp_first_projection := fun _ _ => rfl
      phase_none_eq_comp_second_projection := fun _ => rfl
      base_ph := fun p hp => (hbp p hp).1
      base_phT := fun p hp t => (hbp p hp).2 t
      L' := L'
      v := v
      Dg := Dg
      cst := cst
      potL' := potL'
      secv := secv
      sncv := sncv
      sncsv := sncsv
      normv := normv
      U := U
      B := B
      G := G
      α := α
      ΦY := ΦY
      ΦW := ΦW
      U_open := U_open
      B_meas := B_meas
      G_pos := G_pos
      G_smooth := G_smooth
      α_smooth := fun m p => α_smooth m p
      coverY := coverY
      coverW := coverW
      ΦY_open := ΦY_open
      first_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).1
      second_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).2
      xi_pot := xi_pot
      base_pot := base_pot
      norm_hom := norm_hom }
  have hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w := fun w => by
    have hd := FA.Re.degree
    rw [FA.deg_one, FA.br_empty] at hd
    obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))
    exact ⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩
  refine ⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩
  · intro x x₀ hx
    refine ⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩
    · show RW.lift x x (v₁ k₀ p) = _
      rw [v₁_ne hp]
    · show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _
      rw [v₁_self]
  · intro x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1
    obtain ⟨x₀, hx₀⟩ := hsurj (q 0 x)
    obtain ⟨x₁, hx₁⟩ := hsurj (q 1 x)
    exact hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁))
      hh hd ht hE0 hE1

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_swap_square_system : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists
end
