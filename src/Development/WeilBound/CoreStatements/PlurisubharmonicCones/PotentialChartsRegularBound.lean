import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization

section
open Filter Topology Metric Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt molli shrink polyMax)

namespace LevelTowerAlt.Bdd

theorem isPsh_comp {m n : ℕ} {U : Set (Fin n → ℂ)} {V : Set (Fin m → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    {u : (Fin n → ℂ) → ℝ} (hc : ContinuousOn u U) (hu : IsPsh U u) {F : (Fin m → ℂ) → Fin n → ℂ}
    (hF : AnalyticOnNhd ℂ F V) (hFU : MapsTo F V U) : IsPsh V (fun v => u (F v)) := by
  have hcF : ContinuousOn (fun v => u (F v)) V := hc.comp hF.continuousOn hFU
  refine ⟨hcF.upperSemicontinuousOn, fun z w hd => ?_⟩
  have hl : Continuous fun ζ : ℂ => z + ζ • w := by fun_prop
  have hmaps : MapsTo (fun ζ : ℂ => z + ζ • w) (closedBall 0 1) V := fun ζ hζ => hd ζ (by simpa using hζ)
  have hint : CircleIntegrable (fun ζ : ℂ => u (F (z + ζ • w))) 0 1 :=
    ((hcF.comp hl.continuousOn hmaps).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  refine ⟨hint, le_of_forall_pos_le_add fun η hη => ?_⟩
  have hK : IsCompact ((fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (hF.continuousOn.comp hl.continuousOn hmaps)
  set Kc := (fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1 with hKc
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU
    (by rintro _ ⟨ζ, hζ, rfl⟩; exact hFU (hmaps hζ))
  have huc := (hK.cthickening (r := δ₀)).uniformContinuousOn_of_continuous (hc.mono hsub)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hε : 0 < min δ₀ (δ / 2) := lt_min hδ₀ (half_pos hδ)
  set ε := min δ₀ (δ / 2) with hεd
  obtain ⟨ho, hsm, hp, hb⟩ := (ReciprocityTheory.AnForm.A.mollify_thm n ρ U u hU hu).1 ε hε
  have hball : ∀ x ∈ Kc, closedBall x ε ⊆ cthickening δ₀ Kc := fun x hx =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (closedBall_subset_cthickening hx δ₀)
  have hshr : ∀ x ∈ Kc, x ∈ shrink U ε := fun x hx => (hball x hx).trans hsub
  have hup : ∀ x ∈ Kc, molli ρ ε u x ≤ u x + η := fun x hx => by
    refine (hb x (hshr x hx)).2.trans (csSup_le ⟨_, x, mem_closedBall_self hε.le, rfl⟩ ?_)
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hδu y (hball x hx hy) x (hball x hx (mem_closedBall_self hε.le))
      ((mem_closedBall.1 hy).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ)))
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (u y - u x)]
  have hV' : IsOpen (V ∩ F ⁻¹' shrink U ε) := hF.continuousOn.isOpen_inter_preimage hV ho
  have h2 : ContDiffOn ℝ 2 (molli ρ ε u) (shrink U ε) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm n _ _ ho h2).1 hp
  have hC : ContDiffOn ℝ 2 (molli ρ ε u ∘ F) (V ∩ F ⁻¹' shrink U ε) := fun v hv =>
    ((h2.contDiffAt (ho.mem_nhds hv.2)).comp v
      ((hF v hv.1).restrictScalars (𝕜 := ℝ)).contDiffAt).contDiffWithinAt
  have hP : IsPsh (V ∩ F ⁻¹' shrink U ε) (molli ρ ε u ∘ F) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm m _ _ hV' hC).2 ⟨hC, fun v hv a => by
      rw [ReciprocityTheory.AnForm.levi_comp a (hF v hv.1) (h2.contDiffAt (ho.mem_nhds hv.2))]
      exact hlevi.2 _ hv.2 _⟩
  obtain ⟨hi2, hle⟩ := hP.2 z w fun ζ hζ => ⟨hd ζ hζ, hshr _ ⟨ζ, by simpa using hζ, rfl⟩⟩
  have hz : F z ∈ Kc := ⟨0, mem_closedBall_self zero_le_one, by simp⟩
  have h3 := Real.circleAverage_mono hi2 (hint.add (circleIntegrable_const η 0 1)) fun ζ hζ =>
    hup _ ⟨ζ, sphere_subset_closedBall (by simpa using hζ), rfl⟩
  rw [Real.circleAverage_add hint (circleIntegrable_const η 0 1), Real.circleAverage_const] at h3
  exact ((hb _ (hshr _ hz)).1.trans hle).trans h3

def PH {n : ℕ} (f : (Fin n → ℂ) → ℝ) (v : Fin n → ℂ) : Prop :=
  ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G v ∧ ∀ᶠ u in 𝓝 v, f u = (G u).re

theorem PH.add {n : ℕ} {f g : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (hg : PH g v) :
    PH (fun u => f u + g u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  obtain ⟨G, hG, h2⟩ := hg
  refine ⟨fun u => F u + G u, hF.add hG, ?_⟩
  filter_upwards [h1, h2] with u a b
  rw [a, b, Complex.add_re]

theorem PH.const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (c : ℝ) :
    PH (fun u => c * f u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  refine ⟨fun u => (c : ℂ) * F u, analyticAt_const.mul hF, ?_⟩
  filter_upwards [h1] with u a
  rw [a, Complex.re_ofReal_mul]

theorem PH.sum {n : ℕ} {σ : Type} (s : Finset σ) {f : σ → (Fin n → ℂ) → ℝ} {v : Fin n → ℂ}
    (hf : ∀ i ∈ s, PH (f i) v) : PH (fun u => ∑ i ∈ s, f i u) v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem PH.log_norm {n : ℕ} {F : (Fin n → ℂ) → ℂ} {v : Fin n → ℂ} (hF : AnalyticAt ℂ F v) (h0 : F v ≠ 0) :
    PH (fun u => Real.log ‖F u‖) v := by
  have hH : AnalyticAt ℂ (fun t => F t / F v) v := hF.div analyticAt_const h0
  refine ⟨fun t => Complex.log (F t / F v) + (Real.log ‖F v‖ : ℝ),
    (hH.clog (by rw [div_self h0]; exact Complex.one_mem_slitPlane)).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

theorem local_psh {m n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {φ : (Fin n → ℂ) → ℝ} (hc : ContinuousOn φ U)
    (hφ : IsPsh U φ) {F : (Fin m → ℂ) → Fin n → ℂ} {v : Fin m → ℂ} (hF : AnalyticAt ℂ F v) (hv : F v ∈ U)
    {f g : (Fin m → ℂ) → ℝ} (hf : PH f v) (hg : ∀ᶠ u in 𝓝 v, g u = φ (F u) + f u) :
    ContinuousAt g v ∧ ∃ V, IsOpen V ∧ v ∈ V ∧ IsPsh V g := by
  obtain ⟨G, hG, hfG⟩ := hf
  have he : ∀ᶠ u in 𝓝 v, g u = φ (F u) + (G u).re + 0 := by
    filter_upwards [hg, hfG] with u a b
    rw [a, b, add_zero]
  refine ⟨?_, ?_⟩
  · have h1 : ContinuousAt (fun u => φ (F u) + (G u).re + 0) v :=
      (((hc.continuousAt (hU.mem_nhds hv)).comp hF.continuousAt).add
        (Complex.continuous_re.continuousAt.comp hG.continuousAt)).add continuousAt_const
    exact h1.congr (he.mono fun u h => h.symm)
  · obtain ⟨V, hV, hVo, hvV⟩ := _root_.eventually_nhds_iff.1 ((he.and hF.eventually_analyticAt).and
      (hG.eventually_analyticAt.and (hF.continuousAt.eventually (hU.mem_nhds hv))))
    refine ⟨V, hVo, hvV, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun u hu => (hV u hu).1.1.symm) ?_⟩
    exact GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hVo
      (isPsh_comp hU hVo hc hφ (fun u hu => (hV u hu).1.2) fun u hu => (hV u hu).2.2)
      (fun u hu => (hV u hu).2.1.differentiableAt.differentiableWithinAt) 0

theorem limsup_add_tendsto {α : Type} {l : Filter α} [l.NeBot] {q g : α → ℝ} {a C : ℝ} (hq : Tendsto q l (𝓝 a))
    (hg : ∀ᶠ x in l, |g x| ≤ C) : limsup (fun x => q x + g x) l = a + limsup g l := by
  have g1 : IsBoundedUnder (· ≤ ·) l g := isBoundedUnder_of_eventually_le (hg.mono fun x h => (abs_le.1 h).2)
  have g2 : IsCoboundedUnder (· ≤ ·) l g :=
    isCoboundedUnder_le_of_eventually_le l (hg.mono fun x h => (abs_le.1 h).1)
  refine le_antisymm ?_ ?_
  · have := limsup_add_le hq.isBoundedUnder_ge hq.isBoundedUnder_le g2 g1
    rwa [hq.limsup_eq] at this
  · have := le_limsup_add g1 g2 hq.isBoundedUnder_le hq.isBoundedUnder_ge
    rw [hq.liminf_eq, add_comm, add_comm g q] at this
    exact this

theorem abs_limsup_le {α : Type} {l : Filter α} [l.NeBot] {g : α → ℝ} {C : ℝ}
    (hg : ∀ᶠ x in l, |g x| ≤ C) : |limsup g l| ≤ C :=
  abs_le.2 ⟨le_limsup_of_frequently_le (hg.mono fun _ h => (abs_le.1 h).1).frequently
      (isBoundedUnder_of_eventually_le (hg.mono fun _ h => (abs_le.1 h).2)),
    limsup_le_of_le (isCoboundedUnder_le_of_eventually_le l (hg.mono fun _ h => (abs_le.1 h).1))
      (hg.mono fun _ h => (abs_le.1 h).2)⟩

theorem isPsh_ext {n : ℕ} {T : Set (Fin n → ℂ)} (hT : IsOpen T) (hT1 : T ⊆ ball 0 1) (S : Finset (Fin n))
    {q g g' : (Fin n → ℂ) → ℝ} {C : ℝ} (hq : ContinuousOn q T) (hg : ∀ v ∈ T \ coordDiv S, |g v| ≤ C)
    (hc : ContinuousOn (fun v => q v + g v) (T \ coordDiv S)) (hp : IsPsh (T \ coordDiv S) fun v => q v + g v)
    (h1 : ∀ v ∈ T \ coordDiv S, g' v = g v)
    (h2 : ∀ v ∈ T, v ∈ coordDiv S → g' v = limsup g (𝓝[T \ coordDiv S] v)) :
    IsPsh T fun v => q v + g' v := by
  refine GlobalTheory.T.plurisubharmonic_local n T _ hT fun v₀ hv₀ => ?_
  obtain ⟨δ, hδ, hδT⟩ := nhds_basis_closedBall.mem_iff.1 (hT.mem_nhds hv₀)
  obtain ⟨Mq, hMq⟩ := (isCompact_closedBall v₀ δ).exists_bound_of_continuousOn (hq.mono hδT)
  have hUT : ball v₀ δ ⊆ T := ball_subset_closedBall.trans hδT
  have hD : ball v₀ δ \ coordDiv S ⊆ T \ coordDiv S := sdiff_subset_sdiff_left hUT
  have hab : ∀ v ∈ ball v₀ δ \ coordDiv S, |q v + g v| ≤ Mq + C := fun v hv =>
    (abs_add_le _ _).trans (add_le_add (hMq v (ball_subset_closedBall hv.1)) (hg v (hD hv)))
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm n S (ball v₀ δ) (fun v => q v + g v) |Mq + C| isOpen_ball
    (hUT.trans hT1) (hc.mono hD) (GroundTheory.Heights₂.Heights.Regular.isPsh_mono hp hD) fun y hy => by
      have hy1 : ‖y‖ < 1 := by simpa using hT1 (hUT hy.1)
      have hs : 0 ≤ ∑ i ∈ S, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
        rw [Real.log_inv]
        exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
      have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖y i‖⁻¹) := by
        have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
        rwa [Real.log_exp] at this
      exact (((le_abs_self _).trans (hab y hy)).trans (le_abs_self _)).trans
        (le_mul_of_one_le_right (abs_nonneg _) hL)).2 (Mq + C)
  refine ⟨ball v₀ δ, isOpen_ball, mem_ball_self hδ, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun v hv => ?_) hext⟩
  have hmax : ∀ y ∈ ball v₀ δ \ coordDiv S, max (q y + g y) (-(Mq + C)) = q y + g y := fun y hy =>
    max_eq_left (abs_le.1 (hab y hy)).1
  unfold limsupExt
  split_ifs with hS
  · have hf : 𝓝[ball v₀ δ \ coordDiv S] v = 𝓝[T \ coordDiv S] v :=
      nhdsWithin_eq_nhdsWithin' (isOpen_ball.mem_nhds hv) (Set.ext fun y =>
        ⟨fun h => ⟨hD h.1, h.2⟩, fun h => ⟨⟨h.2, h.1.2⟩, h.2⟩⟩)
    have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hT (hUT hv)
    rw [limsup_congr (v := fun y => q y + g y) (eventually_nhdsWithin_of_forall hmax), hf]
    show _ = q v + g' v
    rw [h2 v (hUT hv) hS]
    exact limsup_add_tendsto ((hq.continuousAt (hT.mem_nhds (hUT hv))).tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hg)
  · show max (q v + g v) (-(Mq + C)) = q v + g' v
    rw [hmax v ⟨hv, hS⟩, h1 v ⟨hUT hv, hS⟩]

end LevelTowerAlt.Bdd
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Bdd

open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular

theorem continuousAt_of_holoOn {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X} {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨i, hi⟩ := A.cover x
  have h1 := (hg i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩).continuousAt
  refine (h1.comp ((A.chart i).continuousAt hi)).congr ?_
  filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
  simp [(A.chart i).left_inv hy]

theorem limsup_invol {X : Type} [TopologicalSpace X] {σ : X → X} (hσ : Continuous σ) (hi : ∀ x, σ (σ x) = x)
    {Y : Set X} (hY : ∀ x ∈ Y, σ x ∈ Y) {g : X → ℝ} (hg : ∀ x ∈ Y, g (σ x) = g x) (x : X) :
    limsup g (𝓝[Y] (σ x)) = limsup g (𝓝[Y] x) := by
  have ht : ∀ x, map σ (𝓝[Y] x) ≤ 𝓝[Y] (σ x) := fun x =>
    (hσ.continuousWithinAt (s := Y) (x := x)).tendsto_nhdsWithin hY
  have he : map σ (𝓝[Y] x) = 𝓝[Y] (σ x) := by
    refine le_antisymm (ht x) ?_
    have h1 := map_mono (m := σ) (ht (σ x))
    rw [Filter.map_map, show σ ∘ σ = id from funext hi, Filter.map_id, hi] at h1
    exact h1
  rw [← he, ← limsup_comp]
  exact limsup_congr (eventually_nhdsWithin_of_forall hg)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (M : XModel D)

theorem smul_inv (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
  funext p
  simp [torusSmul, hc]

theorem bd_iff {z z' : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hz' : z' ∈ mcPts (mCoordIdeal D.y))
    (h : M.proj z = M.proj z') : z ∈ D.Bd ↔ z' ∈ D.Bd := by
  obtain ⟨c, hc, e⟩ := (M.fibre z hz z' hz').1 h
  obtain ⟨c', hc', e'⟩ := (M.fibre z' hz' z hz).1 h.symm
  exact ⟨fun h => e ▸ D.bd_torus z h c hc, fun h => e' ▸ D.bd_torus z' h c' hc'⟩

def Yo : Set M.Xc := {x | (M.surj x).choose ∉ D.Bd}

theorem proj_mem_Yo {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) : M.proj z ∈ Yo M ↔ z ∉ D.Bd :=
  not_congr (bd_iff M (M.surj (M.proj z)).choose_spec.1 hz (M.surj (M.proj z)).choose_spec.2)

noncomputable def ph0 (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (x : M.Xc) : ℝ :=
  w (M.surj x).choose - Real.log (ref.h (M.surj x).choose)

theorem relative_weight_projection {ref : HermLine J} {w : ((Σ k, J k) → ℂ) → ℝ} (hL : LogHom D ref.a w) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ D.Xo) : ph0 M ref w (M.proj z) = w z - Real.log (ref.h z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, e⟩ := (M.fibre z hz.1 _ hw).1 he.symm
  have h2 := SncPiece.logHom_log D ref z hz c hc
  unfold ph0
  rw [e, hL z hz c hc]
  simp only at h2
  rw [h2]
  ring

theorem analyticAt_sec {ψ : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)} (hψ : IsCompatChart M.atlas ψ)
    {U : Set M.Xc} {s : M.Xc → (Σ k, J k) → ℂ} (hs : ∀ p, M.atlas.HoloOn U fun y => s y p) {v : Fin D.n → ℂ}
    (hv : v ∈ ψ.target) (hU : ψ.symm v ∈ U) (p : Σ k, J k) : AnalyticAt ℂ (fun u => s (ψ.symm u) p) v := by
  have h := analyticAt_comp_symm_of_holoOn hψ (hs p) hU (ψ.map_target hv)
  rwa [ψ.right_inv hv] at h

theorem exists_factor {ψ : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)} (hψ : IsCompatChart M.atlas ψ)
    {v : Fin D.n → ℂ} (hv : v ∈ ψ.target) :
    ∃ (a : Fin D.nCharts) (F : (Fin D.n → ℂ) → Fin D.n → ℂ), AnalyticAt ℂ F v ∧
      ∀ᶠ u in 𝓝 v, F u ∈ ball (0 : Fin D.n → ℂ) 1 ∧ M.proj ((D.chart a).γ (F u)) = ψ.symm u := by
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections (ψ.symm v)
  obtain ⟨a, t₀, ht₀, c, hc, e⟩ := D.chart_cover _ (hs _ hx).1
  obtain ⟨V, T, hV, hV0, hT, -, hTz⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a t₀ (mem_ball_zero_iff.2 (by linarith))
  let σ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun u => torusSmul (fun k => (c k)⁻¹) (s (ψ.symm u))
  have hσ : AnalyticAt ℂ σ v := analyticAt_pi_iff.2 fun p => analyticAt_const.mul (analyticAt_sec M hψ hh hv hx p)
  have hσv : σ v ∈ V := by
    change torusSmul _ (s (ψ.symm v)) ∈ V
    rwa [e, smul_inv c hc]
  refine ⟨a, fun u => T (σ u), (hT _ hσv).comp hσ, ?_⟩
  filter_upwards [hσ.continuousAt.eventually (hV.mem_nhds hσv),
    (ψ.continuousAt_symm hv).eventually (hU.mem_nhds hx)] with u h1 h2
  have hm : σ u ∈ mcPts (mCoordIdeal D.y) :=
    mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) (hs _ h2).1
  obtain ⟨hb, c', hc', e'⟩ := hTz _ ⟨h1, hm⟩
  refine ⟨hb, ?_⟩
  rw [(M.fibre _ ((D.chart a).mem _ hb) _ hm).2 ⟨c', hc', e'⟩,
    ← (M.fibre _ (hs _ h2).1 _ hm).2 ⟨_, fun k => inv_ne_zero (hc k), rfl⟩, (hs _ h2).2]

theorem isOpen_nz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const

variable {ref : HermLine J} {w : ((Σ k, J k) → ℂ) → ℝ} (P : PotentialCharts M.atlas)

include P in

theorem relative_weight_bounded (hr : IsSmoothHerm ref) (hL : LogHom D ref.a w) (hB : ChartBdd D w) :
    ∃ C, ∀ y ∈ Yo M, |ph0 M ref w y| ≤ C := by
  have hloc : ∀ x : M.Xc, ∃ C, ∀ᶠ y in 𝓝 x, y ∈ Yo M → |ph0 M ref w y| ≤ C := by
    intro x
    obtain ⟨j, hj⟩ := P.cover x
    have hx := P.mid_subset_source j (P.inner_subset_mid j hj)
    obtain ⟨a, F, hF, hev⟩ := exists_factor M (P.compat j) ((P.chart j).map_source hx)
    have hb := hev.self_of_nhds.1
    obtain ⟨ε, hε, C, hC⟩ := hB a _ hb
    have hm := (D.chart a).mem _ hb
    have hc : ContinuousAt (fun u => Real.log (ref.h ((D.chart a).γ (F u)))) (P.chart j x) :=
      ((hr.continuousOn.continuousAt (isOpen_nz.mem_nhds hm.1)).comp (f := fun u => (D.chart a).γ (F u))
        (((D.chart a).analytic _ hb).continuousAt.comp hF.continuousAt)).log (ref.pos _ hm.1).ne'
    have h3 := (hev.and (hc.eventually (ball_mem_nhds _ one_pos))).and (hF.continuousAt.eventually (ball_mem_nhds _ hε))
    refine ⟨C + (|Real.log (ref.h ((D.chart a).γ (F (P.chart j x))))| + 1), ?_⟩
    filter_upwards [((P.chart j).continuousAt hx).eventually h3, (P.chart j).open_source.mem_nhds hx] with y hy hys hY
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := hy
    rw [(P.chart j).left_inv hys] at h2
    have hm' := (D.chart a).mem _ h1
    have hbd : (D.chart a).γ (F (P.chart j y)) ∉ D.Bd := (proj_mem_Yo M hm').1 (by rw [h2]; exact hY)
    have h6 := hC _ ⟨h1, hbd⟩ ((dist_eq_norm _ _).symm.trans_lt h5)
    have h7 := relative_weight_projection M hL (z := (D.chart a).γ (F (P.chart j y))) ⟨hm', hbd⟩
    rw [h2] at h7
    have h8 : |Real.log (ref.h ((D.chart a).γ (F (P.chart j y)))) -
        Real.log (ref.h ((D.chart a).γ (F (P.chart j x))))| < 1 := h4
    rw [h7]
    refine (abs_sub _ _).trans (add_le_add h6 ?_)
    linarith [abs_sub_abs_le_abs_sub (Real.log (ref.h ((D.chart a).γ (F (P.chart j y)))))
      (Real.log (ref.h ((D.chart a).γ (F (P.chart j x)))))]
  choose C hC using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => {y | y ∈ Yo M → |ph0 M ref w y| ≤ C x})
    fun x _ => hC x
  refine ⟨∑ x ∈ t, |C x|, fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact ((hxy hy).trans (le_abs_self _)).trans (Finset.single_le_sum (fun x _ => abs_nonneg (C x)) hx)

theorem symm_mem_Yo {S : Fin P.N → Finset (Fin D.n)} (hA : Adapted M P S) (j : Fin P.N) {v : Fin D.n → ℂ}
    (hv : v ∈ (P.chart j).target) : (P.chart j).symm v ∈ Yo M ↔ v ∉ coordDiv (S j) :=
  not_congr (hA.mem_bd_iff hv (M.surj _).choose_spec.1 (M.surj _).choose_spec.2.symm)

theorem chart_local (hth : ThRef M ref P.th) (hL : LogHom D ref.a w) (hP : ChartPsh D w) (hC : ChartCont D w)
    (j : Fin P.N) {v : Fin D.n → ℂ} (hv : v ∈ (P.chart j).target) (hY : ∀ᶠ u in 𝓝 v, (P.chart j).symm u ∈ Yo M) :
    ContinuousAt (fun u => P.q j u + ph0 M ref w ((P.chart j).symm u)) v ∧
      ∃ V, IsOpen V ∧ v ∈ V ∧ IsPsh V fun u => P.q j u + ph0 M ref w ((P.chart j).symm u) := by
  classical
  obtain ⟨a, F, hF, hev⟩ := exists_factor M (P.compat j) hv
  have hxs := (P.chart j).map_target hv
  obtain ⟨U, hU, hxU, hUs, s, hs, hh, G, hG, hGe⟩ := hth _ _ (P.th.mem_U ((P.chart j).symm v))
  obtain ⟨W', hW, hxW, G', hG', hGe'⟩ := P.q_th j _ _ ⟨P.th.mem_U ((P.chart j).symm v), hxs⟩
  have a1 := analyticAt_comp_symm_of_holoOn (P.compat j) hG hxU hxs
  have a2 := analyticAt_comp_symm_of_holoOn (P.compat j) hG' hxW hxs
  rw [(P.chart j).right_inv hv] at a1 a2
  have hb := hev.self_of_nhds.1
  have hm := (D.chart a).mem _ hb
  choose i hi using hm.1
  have hγ : ∀ k, AnalyticAt ℂ (fun u => (D.chart a).γ (F u) ⟨k, i k⟩) v := fun k =>
    analyticAt_pi_iff.1 (((D.chart a).analytic _ hb).comp hF) ⟨k, i k⟩
  have hsa := fun k => analyticAt_sec M (P.compat j) hh hv hxU ⟨k, i k⟩
  have hs0 : ∀ k, s ((P.chart j).symm v) ⟨k, i k⟩ ≠ 0 := by
    obtain ⟨c, hc, e⟩ := (M.fibre _ hm _ (hs _ hxU).1).1 (hev.self_of_nhds.2.trans (hs _ hxU).2.symm)
    intro k
    rw [e]
    exact mul_ne_zero (hc k) (hi k)
  have hPH : PH (fun u => (∑ k, (ref.a k : ℝ) *
      Real.log ‖s ((P.chart j).symm u) ⟨k, i k⟩ / (D.chart a).γ (F u) ⟨k, i k⟩‖) +
        ((G ((P.chart j).symm u)).re + (G' ((P.chart j).symm u)).re)) v :=
    (PH.sum _ fun k _ => (PH.log_norm ((hsa k).div (hγ k) (hi k)) (div_ne_zero (hs0 k) (hi k))).const_mul _).add
      (PH.add ⟨_, a1, Eventually.of_forall fun _ => rfl⟩ ⟨_, a2, Eventually.of_forall fun _ => rfl⟩)
  have hbd : ∀ᶠ u in 𝓝 v, F u ∈ offBd D a := by
    filter_upwards [hev, hY] with u h1 h2
    exact ⟨h1.1, (proj_mem_Yo M ((D.chart a).mem _ h1.1)).1 (h1.2 ▸ h2)⟩
  refine local_psh (SncPiece.isOpen_offBd D a) (hC a) (hP a) hF hbd.self_of_nhds hPH ?_
  filter_upwards [hev, hbd, (P.chart j).open_target.mem_nhds hv,
    ((P.chart j).continuousAt_symm hv).eventually (hU.mem_nhds hxU),
    ((P.chart j).continuousAt_symm hv).eventually (hW.mem_nhds hxW),
    eventually_all.2 fun k => (hγ k).continuousAt.eventually_ne (hi k)] with u h1 h2 h3 h4 h5 h6
  have hXo := SncPiece.mem_Xo_of_offBd D h2
  obtain ⟨c, hc, e⟩ := (M.fibre _ hXo.1 _ (hs _ h4).1).1 (h1.2.trans (hs _ h4).2.symm)
  have e1 := hGe _ h4
  have e2 := hGe' _ ⟨⟨h5, hUs h4⟩, (P.chart j).map_target h3⟩
  rw [(P.chart j).right_inv h3] at e2
  have e3 := relative_weight_projection M hL hXo
  rw [h1.2] at e3
  have e4 := SncPiece.logHom_log D ref _ hXo c hc
  simp only at e4
  rw [← e] at e4
  have e5 : ∀ k, s ((P.chart j).symm u) ⟨k, i k⟩ / (D.chart a).γ (F u) ⟨k, i k⟩ = c k := fun k => by
    rw [e]
    exact mul_div_cancel_right₀ _ (h6 k)
  simp only [e5]
  linarith

open Classical in

noncomputable def ph (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (x : M.Xc) : ℝ :=
  if x ∈ Yo M then ph0 M ref w x else limsup (ph0 M ref w) (𝓝[Yo M] x)

theorem map_nhds_Yo {S : Fin P.N → Finset (Fin D.n)} (hA : Adapted M P S) (j : Fin P.N) {v : Fin D.n → ℂ}
    (hv : v ∈ (P.chart j).target) :
    map (P.chart j).symm (𝓝[(P.chart j).target \ coordDiv (S j)] v) = 𝓝[Yo M] ((P.chart j).symm v) := by
  rw [← (P.chart j).symm.map_nhdsWithin_preimage_eq hv]
  congr 1
  exact nhdsWithin_eq_nhdsWithin' ((P.chart j).open_target.mem_nhds hv) (Set.ext fun y =>
    ⟨fun h => ⟨(symm_mem_Yo M P hA j h.2).2 h.1.2, h.2⟩, fun h => ⟨⟨h.2, (symm_mem_Yo M P hA j h.2).1 h.1⟩, h.2⟩⟩)

noncomputable def cj (x : M.Xc) : M.Xc := M.proj (conjVec (M.surj x).choose)

theorem cj_proj {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) : cj M (M.proj z) = M.proj (conjVec z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, e⟩ := (M.fibre z hz _ hw).1 he.symm
  refine ((M.fibre _ (SncPiece.conj_mem hz) _ (SncPiece.conj_mem hw)).2
    ⟨fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩).symm
  rw [e]
  funext p
  simp [conjVec, torusSmul]

theorem continuous_cj : Continuous (cj M) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have h1 : ContinuousAt (fun y => conjVec (s y)) x := continuousAt_pi.2 fun p =>
    Complex.continuous_conj.continuousAt.comp (continuousAt_of_holoOn (hh p) hx)
  have h2 : ContinuousWithinAt (fun y => M.proj (conjVec (s y))) U x :=
    (M.cont _ (SncPiece.conj_mem (hs x hx).1)).comp (f := fun y => conjVec (s y)) h1.continuousWithinAt
      fun y hy => SncPiece.conj_mem (hs y hy).1
  refine (h2.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [← cj_proj M (hs y hy).1, (hs y hy).2]

theorem ph_conj (hL : LogHom D ref.a w) (hr : IsConjInvariantH ref) (hO : ConjOff D w) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) : ph M ref w (M.proj (conjVec z)) = ph M ref w (M.proj z) := by
  have hi : ∀ x, cj M (cj M x) = x := fun x => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    rw [cj_proj M hz, cj_proj M (SncPiece.conj_mem hz), SncPiece.conj_conj]
  have hY : ∀ x, cj M x ∈ Yo M ↔ x ∈ Yo M := fun x => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    rw [cj_proj M hz, proj_mem_Yo M hz, proj_mem_Yo M (SncPiece.conj_mem hz), SncPiece.conj_mem_bd_iff]
  have hg : ∀ x ∈ Yo M, ph0 M ref w (cj M x) = ph0 M ref w x := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    have hz' : z ∈ D.Xo := ⟨hz, (proj_mem_Yo M hz).1 hx⟩
    have e : ref.h (conjVec z) = ref.h z := hr z
    rw [cj_proj M hz, relative_weight_projection M hL hz', relative_weight_projection M hL (SncPiece.conj_mem_Xo D hz'), hO z hz', e]
  rw [← cj_proj M hz]
  unfold ph
  by_cases h : M.proj z ∈ Yo M
  · rw [if_pos h, if_pos ((hY _).2 h), hg _ h]
  · rw [if_neg h, if_neg fun h' => h ((hY _).1 h'),
      limsup_invol (continuous_cj M) hi (fun x hx => (hY x).2 hx) hg]

end LevelTowerAlt.Bdd

open LevelTowerAlt.Bdd in
theorem LevelTowerAlt.potential_charts_regular_bound : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), IsSmoothHerm ref → ThRef M ref P.th → Adapted M P S → LogHom D ref.a w → ChartPsh D w → ChartCont D w → ChartBdd D w → ∃ B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData M.atlas, B.toPotentialCharts = P ∧ (∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), B.ph (M.proj z) = w z - Real.log (ref.h z)) ∧ (IsConjInvariantH ref → ConjOff D w → ∀ z ∈ mcPts (mCoordIdeal D.y), B.ph (M.proj (conjVec z)) = B.ph (M.proj z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M ref w P S hr hth hA hL hP hC hB
  obtain ⟨C, hCb⟩ := relative_weight_bounded M P hr hL hB
  have hloc := fun j v (hv : v ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j)) =>
    chart_local M P hth hL hP hC j hv.1 (by
      filter_upwards [((P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)).mem_nhds hv]
        with u hu
      exact (symm_mem_Yo M P hA j hu.1).2 hu.2)
  refine ⟨{ toPotentialCharts := P, ph := ph M ref w, bdd := ⟨C, fun x => ?_⟩, u_psh := fun j => ?_ }, rfl,
    fun z hz => ?_, fun hr' hO z hz => ph_conj M hL hr' hO hz⟩
  · unfold ph
    split_ifs with h
    · exact hCb x h
    · obtain ⟨j, hj⟩ := P.cover x
      have hx := P.mid_subset_source j (P.inner_subset_mid j hj)
      have h1 := map_nhds_Yo M P hA j ((P.chart j).map_source hx)
      rw [(P.chart j).left_inv hx] at h1
      have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S j) (P.chart j).open_target ((P.chart j).map_source hx)
      have : (𝓝[Yo M] x).NeBot := h1 ▸ inferInstance
      exact abs_limsup_le (eventually_nhdsWithin_of_forall hCb)
  · refine isPsh_ext (P.chart j).open_target (P.target_subset j) (S j)
      (g := fun u => ph0 M ref w ((P.chart j).symm u)) (C := C) (P.q_smooth j).continuousOn
      (fun v hv => hCb _ ((symm_mem_Yo M P hA j hv.1).2 hv.2))
      (fun v hv => (hloc j v hv).1.continuousWithinAt)
      (GlobalTheory.T.plurisubharmonic_local _ _ _ ((P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _))
        fun v hv => (hloc j v hv).2)
      (fun v hv => if_pos ((symm_mem_Yo M P hA j hv.1).2 hv.2)) fun v hv hS => ?_
    show ph M ref w ((P.chart j).symm v) = _
    unfold ph
    rw [if_neg fun h => (symm_mem_Yo M P hA j hv).1 h hS, ← map_nhds_Yo M P hA j hv]
    rfl
  · show ph M ref w (M.proj z) = _
    unfold ph
    rw [if_pos ((proj_mem_Yo M hz.2).2 hz.1.2), relative_weight_projection M hL hz.1]
end
