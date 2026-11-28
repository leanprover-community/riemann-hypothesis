module

import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.WeaklyHolomorphic
import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteDimensional
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Topology.Instances.Matrix
public import Lib.Speed
import Lib.General.Analysis.GaussianIntegral
import Lib.General.Groups.CongruenceSubgroups
import Lib.General.Measure.HaarNormalisation
import Lib.General.Topology

/-!
# Strong operator integrals, analyticity of parameter integrals, and Hua's integral bound

In the strong integral, operator-valued functions are integrated vector by vector, so no
measurability in the operator norm is needed. In the results on analytic families, E is a
finite-dimensional complex normed space, K a compact space and f : E → K → ℂ a family of
functions on K with parameter in E. The file also contains the Schwarz lemma in normed spaces,
holomorphy of dominated parameter integrals, a uniqueness result for analytic functions along
submersions, and Hua's bound for negative powers of determinants.

## Main definitions and results

* `New.strongIntegral`: the operator `x ↦ ∫ y, F y x ∂μ`, when this map is a bounded operator.
* `New.DiscreteSeries.IsAnalyticFamily`: the map x ↦ f(x, ·) into the Banach space C(K, ℂ) is
  analytic at a point.
* `New.DiscreteSeries.IsAnalyticFamily.analyticAt_integral`: then x ↦ ∫ f(x, k) dμ(k) is analytic,
  for a finite Borel measure μ.
* `New.analyticAt_of_eventually_differentiableAt`: a map between finite-dimensional complex spaces
  that is differentiable near p is analytic at p.
* `New.eventually_differentiableAt_integral`: an integral of holomorphic functions of a parameter in
  a finite-dimensional space, dominated by an integrable function, is holomorphic.
* `New.hua_integral_le`: Hua's bound for the integral of a negative power of `|det (M + Yᴴ Y)|`,
  where `Y = X S + A`, over the rows of `X`, one row at a time;
  `New.lintegral_norm_det_add_inv_pow_le` is a cruder form for `Y = S X + c` and at least seven
  columns.

## Relation to the literature

Known result: an upper bound for Hua's determinant integral. The integral is bounded only from
above, with an affine change of the rows, instead of being computed exactly. Source: Hua, Harmonic
Analysis of Functions of Several Complex Variables in the Classical Domains, AMS 1963.
-/

@[expose] public section

/-! ## The strong integral of a family of bounded operators -/

section OperatorIntegral

open MeasureTheory Function

variable {Y X Z : Type*} [MeasurableSpace Y] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  (μ : Measure Y) (F : Y → X →L[ℂ] Z)

/-- The strong integral of a family `F` of bounded operators. If some bounded operator agrees
with the map `x ↦ ∫ y, F y x ∂μ`, this is that operator (`New.strongIntegral_apply_of_exists`;
`invFun (⇑)` picks a preimage under the coercion from operators to functions); otherwise it is an
unspecified operator. The first case holds when every `y ↦ F y x` is integrable and the spaces are
complete (`New.exists_continuousLinearMap_apply_eq_integral`, `New.strongIntegral_apply`). -/
noncomputable def New.strongIntegral : X →L[ℂ] Z := invFun (⇑) fun x ↦ ∫ y : Y, F y x ∂μ

lemma New.rep_apply_apply {G : Type*} [Monoid G] (ρ : G →* X →L[ℂ] X) (g h : G) (v : X) :
    ρ g (ρ h v) = ρ (g * h) v := by
  simp

/-- A complex-linear bounded operator `L` may be applied to the derivative of a curve
`f : ℝ → X`: if `f` has derivative `f'` at `t`, then `L ∘ f` has derivative `L f'` at `t`. -/
lemma HasDerivAt.map_clm {f : ℝ → X} {f' : X} {t : ℝ} (hf : HasDerivAt f f' t) (L : X →L[ℂ] Z) :
    HasDerivAt (fun s : ℝ ↦ L (f s)) (L f') t :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf

/-- If some bounded operator agrees at every point with the map `x ↦ ∫ y, F y x ∂μ`, then so does
the strong integral of `F`. -/
lemma New.strongIntegral_apply_of_exists
    (h_exists : ∃ A : X →L[ℂ] Z, ∀ x : X, A x = ∫ y : Y, F y x ∂μ) (x : X) :
    strongIntegral μ F x = ∫ y : Y, F y x ∂μ := by
  obtain ⟨A, hA⟩ := h_exists
  exact congrFun (invFun_eq ⟨A, funext hA⟩) x

/-- For Banach spaces `X`, `Z` and a family `F` of bounded operators such that `y ↦ F y x` is
integrable for every `x`, the map `x ↦ ∫ y, F y x ∂μ` is a bounded operator. No bound on the
norms of the `F y` is assumed: the closed graph theorem gives the boundedness. -/
lemma New.exists_continuousLinearMap_apply_eq_integral [CompleteSpace X] [CompleteSpace Z]
    (h_int : ∀ x : X, Integrable (fun y : Y ↦ F y x) μ) :
    ∃ A : X →L[ℂ] Z, ∀ x : X, A x = ∫ y : Y, F y x ∂μ := by
  -- The linear map `T : X → L¹(μ, Z)`, `x ↦ fun y ↦ F y x`, has a closed graph, so it is bounded.
  let T : X →ₗ[ℂ] Lp Z 1 μ :=
    { toFun := fun x ↦ (h_int x).toL1
      map_add' := fun v w ↦ by
        simpa only [map_add, Pi.add_def] using Integrable.toL1_add _ _ (h_int v) (h_int w)
      map_smul' := fun c v ↦ by
        simpa only [map_smul, RingHom.id_apply] using Integrable.toL1_smul _ (h_int v) c }
  have h_closed (u : ℕ → X) (x : X) (g : Lp Z 1 μ) (hu : Filter.Tendsto u .atTop (nhds x))
      (hg : Filter.Tendsto (T ∘ u) .atTop (nhds g)) : g = T x := by
    -- Along a subsequence `F y (u n)` tends to `g y` for almost every `y`; it tends to `F y x`
    -- for every `y`.
    have h_measure : TendstoInMeasure μ (fun (n : ℕ) (y : Y) ↦ F y (u n)) .atTop g :=
      (tendstoInMeasure_of_tendsto_Lp hg).congr_left fun n ↦ (h_int (u n)).coeFn_toL1
    obtain ⟨φ, hφ, h_ae⟩ := h_measure.exists_seq_tendsto_ae'
    have h_limit : (fun y : Y ↦ F y x) =ᵐ[μ] g :=
      h_ae.mono fun y hy ↦ tendsto_nhds_unique ((F y).cont.seqContinuous (hu.comp hφ)) hy
    exact Lp.ext ((h_int x).coeFn_toL1.trans h_limit).symm
  -- Compose with the integral on `L¹`.
  refine ⟨L1.integralCLM' ℂ ∘L .ofSeqClosedGraph h_closed, fun v : X ↦ ?_⟩
  change L1.integralCLM' ℂ ((h_int v).toL1) = ∫ y : Y, F y v ∂μ
  rw [integral_eq _ (h_int v), L1.integral_eq' ℂ]

/-- For Banach spaces `X`, `Z` and a family `F` of bounded operators such that `y ↦ F y x` is
integrable for every `x`, the strong integral sends `x` to `∫ y, F y x ∂μ`. -/
lemma New.strongIntegral_apply [CompleteSpace X] [CompleteSpace Z]
    (h_int : ∀ x : X, Integrable (fun y : Y ↦ F y x) μ) (x : X) :
    strongIntegral μ F x = ∫ y : Y, F y x ∂μ :=
  strongIntegral_apply_of_exists μ F (exists_continuousLinearMap_apply_eq_integral μ F h_int) x

end OperatorIntegral

/-!
## Analytic maps into C(K, ℂ) and analyticity of differentiable maps

Point evaluations detect holomorphy on each complex coordinate line. Osgood's lemma then gives
analyticity in all coordinates.
The strong integral `New.strongIntegral` serves here as the functional f ↦ ∫ f dμ on C(K, ℂ)
(`New.strongIntegral_eval`).
-/

namespace New

open MeasureTheory Metric ContinuousMap Module Real Finset

variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {p : E} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace K] [CompactSpace K]
  {f : E → K → ℂ}

/-- Let μ be a finite Borel measure on a compact R₁ space K. The strong integral of the evaluation
functionals `evalCLM ℂ k : g ↦ g k` (see `New.strongIntegral`) sends a continuous f : K → ℂ to
∫ f dμ. -/
lemma strongIntegral_eval {mK : MeasurableSpace K} [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] (f : C(K, ℂ)) :
    strongIntegral μ (evalCLM ℂ) f = ∫ k : K, f k ∂μ :=
  strongIntegral_apply μ (evalCLM ℂ) (fun g ↦ (g.memLp μ ℂ).integrable le_rfl) f

/-- f : E → K → ℂ agrees near a with a map from E to the Banach space C(K, ℂ) that is analytic
at a. -/
def DiscreteSeries.IsAnalyticFamily (f : E → K → ℂ) (a : E) : Prop :=
  ∃ g : E → C(K, ℂ), AnalyticAt ℂ g a ∧ ∀ᶠ x : E in nhds a, g x = f x

omit [FiniteDimensional ℂ E] in
/-- Let E be a complex normed space, K a compact space and μ a finite Borel
measure on K. If x ↦ f(x, ·) is analytic at p ∈ E as a map to C(K, ℂ) (`IsAnalyticFamily f p`), then
its integral against μ is an analytic function of x at p. -/
lemma DiscreteSeries.IsAnalyticFamily.analyticAt_integral {mK : MeasurableSpace K} [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (hf : IsAnalyticFamily f p) :
    AnalyticAt ℂ (fun x : E ↦ ∫ k : K, f x k ∂μ) p := by
  obtain ⟨g, hg, h_eq⟩ := hf
  -- The integral is the continuous functional `strongIntegral μ (evalCLM ℂ)` applied to `g`.
  refine (((strongIntegral μ (evalCLM ℂ)).analyticAt (g p)).comp hg).congr
    (h_eq.mono fun x hx ↦ ?_)
  simp [strongIntegral_eval, hx]

/-- Let E be a finite-dimensional complex normed space and K a compact space. If, for all x near
p ∈ E and all k ∈ K, f : E → K → ℂ is jointly continuous at (x, k) and f(·, k) is complex
differentiable at x, then x ↦ f(x, ·) is analytic at p as a map to the Banach space C(K, ℂ), that
is, `IsAnalyticFamily f p`. -/
lemma isAnalyticFamily_of_continuousAt_of_differentiableAt {f : E → K → ℂ} {p : E}
    (hf_cont : ∀ᶠ x : E in nhds p, ∀ k : K, ContinuousAt f.uncurry (x, k))
    (hf_diff : ∀ᶠ x : E in nhds p, ∀ k : K, DifferentiableAt ℂ (fun z : E ↦ f z k) x) :
    DiscreteSeries.IsAnalyticFamily f p := by
  obtain ⟨U, hU, hU_open, hp⟩ := _root_.eventually_nhds_iff.1 (hf_cont.and hf_diff)
  let g (x : E) := ContinuousMap.mkD (f x) 0
  have hc : ContinuousOn f.uncurry (U ×ˢ Set.univ) :=
    fun ⟨x, k⟩ hx ↦ ((hU x hx.1).1 k).continuousWithinAt
  have hg : ContinuousOn g U := ContinuousMap.continuousOn_mkD_of_uncurry f 0 hc
  have heq (x : E) (hx : x ∈ U) (k : K) : g x k = f x k :=
    ContinuousMap.mkD_apply_of_continuous (hc.comp_continuous (Continuous.prodMk_right x)
      (fun _ ↦ ⟨hx, Set.mem_univ _⟩))
  refine ⟨g, ?_, Filter.eventually_of_mem (hU_open.mem_nhds hp) fun x hx ↦ funext (heq x hx)⟩
  let e := (Module.finBasis ℂ E).equivFunL
  have h : AnalyticAt ℂ (g ∘ e.symm) (e p) := by
    apply ContinuousOn.analyticAt_of_differentiableAt_update
      (hg.comp e.symm.continuous.continuousOn (Set.mapsTo_preimage _ _))
      (e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU_open.mem_nhds hp))
    intro y hy i
    let line (z : ℂ) := e.symm (Function.update y i z)
    have hline : Differentiable ℂ line :=
      e.symm.differentiable.comp ((contDiff_update 1 y i).differentiable (by simp))
    have hopen : IsOpen (line ⁻¹' U) := hU_open.preimage hline.continuous
    have hd := TauCeti.differentiableOn_of_continuousOn_of_forall_comp (evalCLM ℂ)
      (fun h hh ↦ ContinuousMap.ext hh) (hg.comp hline.continuous.continuousOn
        (Set.mapsTo_preimage _ _)) (fun k ↦ ?_) hopen
    · exact hd.differentiableAt (hopen.mem_nhds (by simpa [line] using hy))
    · apply DifferentiableOn.congr _ (fun z hz ↦ heq (line z) hz k)
      intro z hz
      exact (((hU (line z) hz).2 k).comp z (hline z)).differentiableWithinAt
  simpa only [Function.comp_def, e.symm_apply_apply] using h.comp (e.analyticAt p)

/-- Let E be a finite-dimensional complex normed space, K a compact space and f : E → K → ℂ. If,
for all x near p ∈ E and all k ∈ K, f is jointly continuous at (x, k) and f(·, k) is complex
differentiable at x, then x ↦ f(x, ·) is analytic at p as a map to C(K, ℂ). The two hypotheses of
`New.isAnalyticFamily_of_continuousAt_of_differentiableAt` are here joined in one. -/
lemma isAnalyticFamily_of_differentiable
    (hf : ∀ᶠ x : E in nhds p, ∀ k : K,
      ContinuousAt f.uncurry (x, k) ∧ DifferentiableAt ℂ (fun z : E ↦ f z k) x) :
    DiscreteSeries.IsAnalyticFamily f p :=
  isAnalyticFamily_of_continuousAt_of_differentiableAt (hf.mono fun _ hx k ↦ (hx k).1)
    (hf.mono fun _ hx k ↦ (hx k).2)

/-- Let E be a finite-dimensional complex normed space and F a complex normed space. If ι : K → F is
continuous, K is compact, and Θ is analytic at (p, ι k) for every k, then x ↦ Θ(x, ι ·) is
analytic at p ∈ E as a map to C(K, ℂ), that is, an `IsAnalyticFamily` at p. -/
lemma DiscreteSeries.IsAnalyticFamily.of_analyticAt {ι : K → F} (hι : Continuous ι)
    (Θ : E × F → ℂ) (hΘ : ∀ k : K, AnalyticAt ℂ Θ (p, ι k)) :
    IsAnalyticFamily (fun (x : E) (k : K) ↦ Θ (x, ι k)) p := by
  -- By compactness of `K`, `Θ` is analytic at `(x, ι k)` for all `k` and all `x` near `p`.
  have h_near : ∀ᶠ x : E in nhds p, ∀ k : K, AnalyticAt ℂ Θ (x, ι k) := by
    simpa using isCompact_univ.eventually_forall_mem (fun x k ↦ (x, ι k))
      {y | AnalyticAt ℂ Θ y} fun k _ ↦ (hΘ k).eventually_analyticAt
  refine isAnalyticFamily_of_continuousAt_of_differentiableAt ?_
    (h_near.mono fun x hx k ↦ (hx k).differentiableAt.comp x (by fun_prop))
  filter_upwards [h_near] with x hx k
  have h_an : AnalyticAt ℂ Θ (x, ι k) := hx k
  fun_prop

/-- Let E and F be finite-dimensional complex normed spaces. A map f : E → F that is complex
differentiable at every point near p is analytic at p. -/
lemma analyticAt_of_eventually_differentiableAt [FiniteDimensional ℂ F] {f : E → F}
    (hf : ∀ᶠ z : E in nhds p, DifferentiableAt ℂ f z) :
    AnalyticAt ℂ f p :=
  have := FiniteDimensional.completeSpace ℂ F
  DifferentiableOn.analyticAt_of_finiteDimensional
    (s := {z | DifferentiableAt ℂ f z}) (fun _ hz ↦ hz.differentiableWithinAt) hf

/-- A complex polynomial P in finitely many variables is differentiable at every x, with
derivative v ↦ ∑ᵢ (∂P/∂Xᵢ)(x)·vᵢ, given by the formal partial derivatives. -/
@[fun_prop]
lemma hasFDerivAt_mvPolynomial_eval {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) (x : ι → ℂ) :
    HasFDerivAt (𝕜 := ℂ) (P.eval ·) (∑ i : ι, (P.pderiv i).eval x • .proj i) x :=
  P.hasFDerivAt_eval x

end New

/-! ## The Schwarz lemma, holomorphic parameter integrals, Mellin integrals -/

section HolomorphicIntegral

open Complex MeasureTheory Metric Module Set

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [MeasurableSpace X] {μ : Measure X}

/-- A map differentiable at zero agrees with its derivative if it commutes with scaling
by a scalar of norm greater than one. -/
lemma New.eq_fderiv_of_smul {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (P : V → W) (hP : DifferentiableAt 𝕜 P 0) {a : 𝕜} (ha : 1 < ‖a‖)
    (h_scale : ∀ x, P (a • x) = a • P x) (w : V) : P w = fderiv 𝕜 P 0 w := by
  have ha₀ : a ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans ha)
  have ha₁ : a ≠ 1 := by
    intro h
    simp [h] at ha
  have h_zero : P 0 = 0 := by
    have h : (a - 1) • P 0 = 0 := by
      rw [sub_smul, one_smul, ← h_scale, smul_zero, sub_self]
    exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha₁)
  have h_inverse (x : V) : a • P (a⁻¹ • x) = P x := by
    rw [← h_scale, smul_inv_smul₀ ha₀]
  -- The difference quotients along the shrinking vectors `(a ^ n)⁻¹ • w` all equal `P w`.
  have quotient_eq (n : ℕ) : a ^ n • (P (0 + (a ^ n)⁻¹ • w) - P 0) = P w := by
    rw [zero_add, h_zero, sub_zero]
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_inv_rev, mul_smul, mul_smul, h_inverse, ih]
  have h_norm : Filter.Tendsto (fun n : ℕ ↦ ‖a ^ n‖) .atTop .atTop := by
    simpa only [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt ha
  exact tendsto_const_nhds_iff.1 ((hP.hasFDerivAt.lim w h_norm).congr quotient_eq)

/-- Schwarz lemma, at the centre of a ball: if a map f between complex normed spaces is complex
differentiable and of norm at most B on the open ball of radius r about c, then
‖f(z) − f(c)‖ ≤ (2B/r)·‖z − c‖ for z in that ball. -/
lemma New.norm_sub_le_of_holomorphic_bdd {f : E → F} {c : E} {r B : ℝ}
    (hf_diff : DifferentiableOn ℂ f (ball c r)) (hf_bound : ∀ w ∈ ball c r, ‖f w‖ ≤ B) {z : E}
    (hz : z ∈ ball c r) :
    ‖f z - f c‖ ≤ 2 * B / r * ‖z - c‖ := by
  have hc : c ∈ ball c r := mem_ball_self (pos_of_mem_ball hz)
  have h_maps : MapsTo f (ball c r) (closedBall (f c) (2 * B)) := fun w hw ↦
    mem_closedBall_iff_norm.2
      ((norm_sub_le_of_le (hf_bound w hw) (hf_bound c hc)).trans_eq (two_mul B).symm)
  simpa [dist_eq_norm] using dist_le_div_mul_dist_of_mapsTo_ball hf_diff h_maps hz

/-- Holomorphy of a parameter integral, the parameter `w` lying in a finite-dimensional space `E`.
Let each `f w : X → F` be a.e. strongly measurable for the measure `μ`, and for all `w` near `z`
and all `x` let `f · x` be complex differentiable at `w` with `‖f w x‖ ≤ g x`, `g` integrable.
Then `w ↦ ∫ f w x dμ` is differentiable at all `w` near `z`. -/
lemma New.eventually_differentiableAt_integral {f : E → X → F} {z : E} {g : X → ℝ}
    [FiniteDimensional ℂ E] (hg : Integrable g μ) (hf : ∀ w : E, AEStronglyMeasurable (f w) μ)
    (h_dom : ∀ᶠ w : E in nhds z, ∀ x : X, DifferentiableAt ℂ (f · x) w ∧ ‖f w x‖ ≤ g x) :
    ∀ᶠ w : E in nhds z, DifferentiableAt ℂ (fun u : E ↦ ∫ x : X, f u x ∂μ) w := by
  -- Differentiate under the integral sign at each point `w` near which the hypothesis holds;
  -- the Schwarz lemma turns the bound `g` on a ball of radius `r` about `w` into the bound
  -- `2 g / r * ‖u - w‖` for `‖f u - f w‖`.
  filter_upwards [h_dom.eventually_nhds] with w hw
  obtain ⟨r, hr, h_ball⟩ :
      ∃ r > 0, ∀ u ∈ ball w r, ∀ x : X, DifferentiableAt ℂ (f · x) u ∧ ‖f u x‖ ≤ g x :=
    eventually_nhds_iff_ball.1 hw
  choose h_diff h_le using h_ball
  have hw_mem : w ∈ ball w r := mem_ball_self hr
  have h_deriv : ∀ᵐ x ∂μ, HasFDerivAt (f · x) (fderiv ℂ (f · x) w) w :=
    ae_of_all μ fun x ↦ (h_diff w hw_mem x).hasFDerivAt
  -- Each directional derivative is a limit of difference quotients, so it is measurable in `x`.
  have h_dir (y : E) : AEStronglyMeasurable (fun x ↦ fderiv ℂ (f · x) w y) μ :=
    aestronglyMeasurable_of_tendsto_ae _ (by fun_prop)
      (h_deriv.mono fun _ hx ↦ (hx.hasLineDerivAt y).tendsto_slope_zero)
  have h_int : Integrable (f w) μ := hg.mono' (hf w) (ae_of_all μ (h_le w hw_mem))
  have h_lip : ∀ᵐ x ∂μ, ∀ u ∈ ball w r, ‖f u x - f w x‖ ≤ 2 * g x / r * ‖u - w‖ :=
    .of_forall fun x u hu ↦ norm_sub_le_of_holomorphic_bdd (f := fun v : E ↦ f v x)
      (fun v hv ↦ (h_diff v hv x).differentiableWithinAt) (fun v hv ↦ h_le v hv x) hu
  have h_hasFDerivAt :
      HasFDerivAt (fun u : E ↦ ∫ x, f u x ∂μ) (∫ x, fderiv ℂ (f · x) w ∂μ) w :=
    (hasFDerivAt_integral_of_dominated_loc_of_lip' (ball_mem_nhds w hr) (fun u _ ↦ hf u) h_int
      (TauCeti.aestronglyMeasurable_clm_apply_iff.mpr h_dir) h_lip (by fun_prop) h_deriv).2
  exact h_hasFDerivAt.differentiableAt

/-- A Mellin integral that converges at two points converges between them. Let N > 0 be a
measurable function on X and T a complex-valued function on X. If the norm of T·N^s has finite
integral and T·N^t is integrable for μ, then T·N^z is integrable for real z in [s, t], and
z ↦ ∫ T·N^z dμ is continuous on [s, t] and real-analytic on (s, t). -/
lemma New.analyticOnNhd_integral_mul_rpow {T : X → ℂ} {N : X → ℝ} {s t : ℝ}
    (hN_pos : ∀ a : X, 0 < N a) (hN : Measurable N)
    (hs : HasFiniteIntegral (fun a : X ↦ T a * (N a ^ s : ℝ)) μ)
    (ht : Integrable (fun a : X ↦ T a * (N a ^ t : ℝ)) μ) :
    (∀ z ∈ Icc s t, Integrable (fun a : X ↦ T a * (N a ^ z : ℝ)) μ) ∧
      ContinuousOn (fun z : ℝ ↦ ∫ a : X, T a * (N a ^ z : ℝ) ∂μ) (Icc s t) ∧
      AnalyticOnNhd ℝ (fun z : ℝ ↦ ∫ a : X, T a * (N a ^ z : ℝ) ∂μ) (Ioo s t) := by
  -- For complex `z` the integrand is entire in `z`; in the strip `s ≤ re z ≤ t` it is dominated
  -- by the sum of the norms of the two integrands at the ends.
  simp_rw [ofReal_cpow (hN_pos _).le] at hs ht ⊢
  have h_ne (a : X) : (N a : ℂ) ≠ 0 := ofReal_ne_zero.2 (hN_pos a).ne'
  have h_factor (z : ℂ) (a : X) : T a * N a ^ (t : ℂ) * N a ^ (z - t) = T a * N a ^ z := by
    rw [mul_assoc, ← cpow_add _ _ (h_ne a), add_sub_cancel]
  have h_meas (z : ℂ) : AEStronglyMeasurable (fun a ↦ T a * N a ^ z) μ :=
    (ht.aestronglyMeasurable.fun_mul
      (hN.complex_ofReal.pow_const (z - t)).aestronglyMeasurable).congr (.of_forall (h_factor z))
  have hs_int : Integrable (fun a ↦ T a * N a ^ (s : ℂ)) μ := ⟨h_meas s, hs⟩
  let bound (a : X) : ℝ := ‖T a * N a ^ (s : ℂ)‖ + ‖T a * N a ^ (t : ℂ)‖
  have h_bound : Integrable bound μ := hs_int.norm.add ht.norm
  have h_strip (z : ℂ) (hz : z.re ∈ Icc s t) (a : X) :
      DifferentiableAt ℂ (fun w ↦ T a * N a ^ w) z ∧ ‖T a * N a ^ z‖ ≤ bound a := by
    have ha : 0 < N a := hN_pos a
    refine ⟨by fun_prop (disch := simp [h_ne]), ?_⟩
    suffices h_real : ‖T a‖ * N a ^ z.re ≤ ‖T a‖ * N a ^ s + ‖T a‖ * N a ^ t by
      simpa only [bound, norm_mul, norm_cpow_eq_rpow_re_of_pos ha, ofReal_re] using h_real
    -- `N a ^ re z` increases or decreases in `re z`, according as `1 ≤ N a` or `N a ≤ 1`
    obtain h_one | h_one := le_total 1 (N a)
    · exact le_add_of_nonneg_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h_one hz.2) (norm_nonneg _))
    · exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ha h_one hz.1) (norm_nonneg _)) (by positivity)
  have h_dom (z : ℝ) (hz : z ∈ Icc s t) : ∀ᵐ a ∂μ, ‖T a * N a ^ (z : ℂ)‖ ≤ bound a :=
    ae_of_all μ fun a ↦ (h_strip z hz a).2
  refine ⟨fun z hz ↦ h_bound.mono' (h_meas z) (h_dom z hz), ?_, fun z hz ↦ ?_⟩
  · exact continuousOn_of_dominated (fun z _ ↦ h_meas z) h_dom h_bound
      (.of_forall fun a ↦ .const_mul (.const_cpow (by fun_prop) (.inl (h_ne a))) (T a))
  · -- The integral is complex differentiable near an inner point, hence analytic there;
    -- restrict to the real line.
    have h_near : ∀ᶠ w in nhds (z : ℂ), w.re ∈ Icc s t := continuous_re.tendsto z (by simpa)
    exact (analyticAt_of_eventually_differentiableAt (eventually_differentiableAt_integral h_bound
      h_meas (h_near.mono h_strip))).restrictScalars.comp (ofRealCLM.analyticAt z)

end HolomorphicIntegral

/-!
## Submodules as complex normed spaces

A submodule of a complex normed space is a normed space over ℂ, for the seminormed group structure
that comes from its normed group structure.
-/

noncomputable instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : Submodule ℂ E) :
    @NormedSpace ℂ V _ NormedAddCommGroup.toSeminormedAddCommGroup := V.normedSpace

/-! ## Analytic functions vanishing on the image of a submersion -/

/-- Let E, F be complex Banach spaces, G entire on F, and f : E → F strictly differentiable at a
with surjective derivative. If G ∘ f vanishes near a, then G = 0. -/
lemma New.eq_zero_of_submersion {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {G : F → ℂ}
    {f : E → F} {f' : E →L[ℂ] F} {a : E} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (h_vanish : ∀ᶠ x : E in nhds a, G (f x) = 0) (y : F) : G y = 0 := by
  -- The map `f` sends neighbourhoods of `a` onto neighbourhoods of `f a`.
  have h_near : ∀ᶠ z in nhds (f a), G z = 0 := by
    rwa [← hf.map_nhds_eq_of_surj hf', Filter.eventually_map]
  exact congrFun (hG.eq_of_eventuallyEq analyticOnNhd_const h_near) y

/-!
## Hua's integral bound

The integrals are lower Lebesgue integrals with values in `[0, ∞]`.
-/

section HuaIntegral

open ComplexOrder Fintype Function Matrix MatrixOrder MeasureTheory Real

/-- For a square matrix C over ℂ and a row vector y, |det (C⋆C + (yC)⋆(yC))| = |det C|² (1 + |y|²),
where ⋆ is the conjugate transpose. -/
lemma New.norm_det_star_mul_self_add_vecMulVec {κ : Type} [Fintype κ] [DecidableEq κ]
    {C : Matrix κ κ ℂ} (y : κ → ℂ) :
    ‖(star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C)).det‖ =
      ‖C.det‖ ^ 2 * (1 + ∑ j : κ, ‖y j‖ ^ 2) := by
  have h_factor : star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C) =
      star C * (1 + vecMulVec (star y) y) * C := by
    simp [mul_add, add_mul, star_vecMul, mul_vecMulVec, vecMulVec_mul, star_eq_conjTranspose]
  -- the matrix determinant lemma: `det (1 + y⋆ y) = 1 + y y⋆`
  have h_det : (1 + vecMulVec (star y) y).det = (1 + ∑ j, ‖y j‖ ^ 2 : ℝ) := by
    simp [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct, RCLike.mul_conj]
  rw [h_factor, det_mul, det_mul, h_det, star_eq_conjTranspose, det_conjTranspose, norm_mul,
    norm_mul, norm_star, Complex.norm_of_nonneg (by positivity)]
  ring

/-- The integral of (1 + |y|²)^{−(k+1)} over y ∈ ℂ^κ, k the number of elements of κ, is π^k/k!. -/
lemma New.lintegral_one_add_sum_norm_sq_inv_pow {κ : Type} [Fintype κ] :
    ∫⁻ y : κ → ℂ, ENNReal.ofReal ((1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) =
      ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
  -- `lintegral_inv_add_rpow` with exponent `k + 1` in complex dimension `k = card κ`
  simp_rw [← rpow_natCast _ (card κ + 1)]
  rw [lintegral_inv_add_rpow one_pos (by simp) (fun y ↦ by positivity) (by positivity)]
  simp [Gamma_nat_eq_factorial]

/-- One row of Hua's bound. Let `M` be positive definite and `S` invertible, both of size `k ≤ r`,
and put `w = v S + a` for a row vector `v` in `ℂ ^ k`. The integral of
`|det (M + wᴴ w)| ^ (-(r + 1))` over `v` is at most `π ^ k / (k! |det S|²) |det M| ^ (-r)`. -/
lemma New.lintegral_norm_det_add_vecMulVec_inv_pow_le {κ : Type} [Fintype κ] [DecidableEq κ]
    {M S : Matrix κ κ ℂ} (hM : M.PosDef) (hS : det S ≠ 0) (a : κ → ℂ) {r : ℕ} (hr : card κ ≤ r) :
    ∫⁻ v : κ → ℂ,
        ENNReal.ofReal (‖(M + vecMulVec (star (v ᵥ* S + a)) (v ᵥ* S + a)).det‖⁻¹ ^ (r + 1)) ≤
      ENNReal.ofReal (π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2 * ‖M.det‖⁻¹ ^ r) := by
  -- With `M = C⋆ C`, substitute `v` so that `v S + a = y C`; then the determinant has absolute
  -- value `|det C|² (1 + |y|²)`.
  obtain ⟨C, hC_unit, rfl⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hM.isStrictlyPositive
  have hC : C.det ≠ 0 := (C.isUnit_iff_isUnit_det.1 hC_unit).ne_zero
  have h_subst (y : κ → ℂ) : ((C * S⁻¹)ᵀ *ᵥ y + -a ᵥ* S⁻¹) ᵥ* S + a = y ᵥ* C := by
    rw [mulVec_transpose]
    simp [add_vecMul, hS]
  let B : ℝ := ‖(star C * C).det‖⁻¹ ^ r / ‖S.det‖ ^ 2
  -- The Jacobian `|det C / det S|²` cancels one factor `|det C|²`.
  have h_jacobian (u : ℝ) :
      ‖(C * S⁻¹)ᵀ.det‖ ^ 2 * (‖C.det‖ ^ 2 * u)⁻¹ ^ (r + 1) = B * u⁻¹ ^ (r + 1) := by
    simp [B, pow_succ _ r, star_eq_conjTranspose, mul_pow, field, ← pow_mul, mul_comm 2 r]
  calc
    _ = ∫⁻ y : κ → ℂ, .ofReal (‖(C * S⁻¹)ᵀ.det‖ ^ 2) *
          .ofReal ((‖C.det‖ ^ 2 * (1 + ∑ j, ‖y j‖ ^ 2))⁻¹ ^ (r + 1)) := by
      rw [← lintegral_add_right_eq_self _ (-a ᵥ* S⁻¹),
        lintegral_eq_norm_det_sq_mul_lintegral_mulVec (C * S⁻¹)ᵀ (by simp [hC, hS]),
        ← lintegral_const_mul' _ _ (by finiteness)]
      simp_rw [h_subst, norm_det_star_mul_self_add_vecMulVec (C := C)]
    _ ≤ ∫⁻ y : κ → ℂ, .ofReal B * .ofReal ((1 + ∑ j, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) := by
      refine lintegral_mono fun y ↦ ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h_jacobian]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))) (Nat.succ_le_succ hr)
    _ = .ofReal (π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2 * ‖(star C * C).det‖⁻¹ ^ r) := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_one_add_sum_norm_sq_inv_pow,
        ← ENNReal.ofReal_mul (by positivity)]
      simp only [B]
      ring_nf

/-- Hua's integral bound. Let `M` be positive definite and `S` invertible, both of size `k`, let
`c ≥ 0`, `r ≥ k`, and put `w i = y i S + a i` for row vectors `y i` in `ℂ ^ k`. The integral of
`c |det (M + ∑_{i ∈ s} (w i)ᴴ (w i))| ^ (-(|s| + r))` over the rows `y i`, `i ∈ s`, is at most
`c (π ^ k / (k! |det S|²)) ^ |s| |det M| ^ (-r)`. The argument `x` of the iterated integral
`∫⋯∫⁻_s` (`MeasureTheory.lmarginal`) fixes the rows outside `s`, which do not occur in the
integrand. -/
lemma New.hua_integral_le {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℂ} (S : Matrix κ κ ℂ) (hS : det S ≠ 0) (a : ι → κ → ℂ) (hM : M.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (s : Finset ι) {r : ℕ} (hr : card κ ≤ r) (x : ι → κ → ℂ) :
    (∫⋯∫⁻_s, fun y : ι → κ → ℂ ↦ ENNReal.ofReal (c *
        ‖(M + ∑ i ∈ s, vecMulVec (star (y i ᵥ* S + a i)) (y i ᵥ* S + a i)).det‖⁻¹ ^
          (s.card + r))) x ≤
      ENNReal.ofReal
        (c * ((π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2) ^ s.card * ‖M.det‖⁻¹ ^ r)) := by
  -- Induction on the set `s` of rows; each row contributes one factor `K`.
  set K : ℝ := π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2
  have hK : 0 ≤ K := by positivity
  induction s using Finset.induction generalizing M r x with
  | empty => simp
  | insert i s hi ih =>
    -- Integrate over the rows in `s` first, the row `v` with index `i` being absorbed into `M`:
    -- the induction hypothesis for `M' v = M + wᴴ w`, `w = v S + a i`, and `r + 1` bounds the inner
    -- integral.
    let F (A : Matrix κ κ ℂ) (t : Finset ι) (n : ℕ) (x' : ι → κ → ℂ) : ENNReal :=
      .ofReal (c *
        ‖(A + ∑ j ∈ t, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)).det‖⁻¹ ^ n)
    let M' (v : κ → ℂ) : Matrix κ κ ℂ := M + vecMulVec (star (v ᵥ* S + a i)) (v ᵥ* S + a i)
    have h_pos (v : κ → ℂ) : (M' v).PosDef := hM.add_posSemidef (posSemidef_vecMulVec_star_self _)
    have inner_eq (v : κ → ℂ) :
        (∫⋯∫⁻_s, F M (insert i s) ((insert i s).card + r)) (update x i v) =
          (∫⋯∫⁻_s, F (M' v) s (s.card + (r + 1))) (update x i v) :=
      -- the row with index `i ∉ s` is not integrated, so it is `v` in the integrand
      lintegral_congr fun y ↦ by simp [F, M', updateFinset, hi, add_assoc, add_comm 1 r]
    calc
      _ = ∫⁻ v : κ → ℂ, (∫⋯∫⁻_s, F M (insert i s) ((insert i s).card + r)) (update x i v) :=
        lmarginal_insert _ (by fun_prop) hi x
      _ ≤ ∫⁻ v : κ → ℂ, .ofReal (c * (K ^ s.card * ‖(M' v).det‖⁻¹ ^ (r + 1))) :=
        lintegral_mono fun v ↦ (inner_eq v).trans_le
          (ih (h_pos v) (Nat.le_succ_of_le hr) (update x i v))
      _ = .ofReal (c * K ^ s.card) * ∫⁻ v : κ → ℂ, .ofReal (‖(M' v).det‖⁻¹ ^ (r + 1)) := by
        simp_rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg hK s.card))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ .ofReal (c * K ^ s.card) * .ofReal (K * ‖M.det‖⁻¹ ^ r) := by
        gcongr
        exact lintegral_norm_det_add_vecMulVec_inv_pow_le hM hS (a i) hr
      _ = .ofReal (c * (K ^ (insert i s).card * ‖M.det‖⁻¹ ^ r)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Finset.card_insert_of_notMem hi]
        ring_nf

/-- The volume `π ^ k / k!` of the unit ball of `ℂ ^ k` is at most `1` for `k ≥ 7`. -/
lemma New.pi_pow_div_factorial_le_one {k : ℕ} (hk : 7 ≤ k) : π ^ k / k.factorial ≤ 1 := by
  rw [div_le_one (by positivity)]
  induction k, hk using Nat.le_induction with
  | base =>
    grw [pi_lt_d2]
    norm_num [Nat.factorial]
  | succ k hk ih =>
    have h_le : π ≤ k + 1 := by linarith [pi_le_four, (Nat.ofNat_le_cast.2 hk : (7 : ℝ) ≤ k)]
    rw [pow_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    gcongr

/-- For an invertible matrix `S` and a measurable `g`, the substitution `A ↦ S A + c` on matrices
with rows in `ℂ ^ κ` multiplies `∫⁻ g` by `|det S| ^ (-2 #κ)`. -/
lemma New.lintegral_comp_mul_add {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) {g : (ι → κ → ℂ) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ A : ι → κ → ℂ, g (S * of A + c) =
      ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ A : ι → κ → ℂ, g A := by
  -- In the coordinates `ι × κ` the map `A ↦ S A` is given by the Kronecker product of `S` and `1`.
  classical
  let e : (ι × κ → ℂ) ≃ₗ[ℂ] (ι → κ → ℂ) := LinearEquiv.curry ℂ ℂ ι κ
  let f : (ι → κ → ℂ) →ₗ[ℂ] (ι → κ → ℂ) :=
    e.toLinearMap ∘ₗ (kroneckerMap (· * ·) S (1 : Matrix κ κ ℂ)).toLin' ∘ₗ e.symm.toLinearMap
  have hf (A : ι → κ → ℂ) : f A = S * of A := by
    ext a b
    simp [f, e, mulVec, dotProduct, Matrix.mul_apply, sum_prod_type, Matrix.one_apply]
  have h_det : LinearMap.det (f.restrictScalars ℝ) = ‖S.det‖ ^ (2 * card κ) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_conj]
    simp [det_kronecker, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, ← pow_mul, mul_comm]
  have h_pos : 0 < ‖S.det‖ ^ (2 * card κ) := pow_pos (norm_pos_iff.2 hS) _
  calc
    _ = ∫⁻ A : ι → κ → ℂ, g (f.restrictScalars ℝ A + of.symm c) :=
      lintegral_congr fun A ↦ congrArg g (congrArg (· + c) (hf A).symm)
    _ = ∫⁻ A, g (A + of.symm c) ∂(Measure.map (f.restrictScalars ℝ) volume) :=
      (lintegral_map (hg.comp (measurable_add_const _))
        (f.restrictScalars ℝ).continuous_of_finiteDimensional.measurable).symm
    _ = _ := by
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (h_det.trans_ne h_pos.ne'),
        lintegral_smul_measure, lintegral_add_right_eq_self, h_det,
        abs_of_pos (inv_pos.2 h_pos), inv_pow, smul_eq_mul]

/-- For fixed matrices `S`, `c`, `G` the map `A ↦ det (G + (S A + c)ᴴ (S A + c))` is measurable. -/
lemma New.measurable_det_add_conjTranspose_mul {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (S : Matrix ι ι ℂ) (c : Matrix ι κ ℂ) (G : Matrix κ κ ℂ) :
    Measurable fun A : ι → κ → ℂ ↦ (G + (S * of A + c)ᴴ * (S * of A + c)).det :=
  Continuous.measurable (by fun_prop)

/-- Hua's bound over matrices. Let `v = S A + c` with `S` invertible, where the rows of `A`
run through `ℂ ^ κ` and `#κ ≥ 7`, and let `G` be positive definite. The integral of
`C |det (G + vᴴ v)| ^ (-(#κ + #ι))` is at most `C |det S| ^ (-2 #κ) |det G| ^ (-#κ)`. -/
lemma New.lintegral_norm_det_add_inv_pow_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) {G : Matrix κ κ ℂ}
    (hG : G.PosDef) {C : ℝ} (hC : 0 ≤ C) (hκ : 7 ≤ card κ) :
    ∫⁻ A : ι → κ → ℂ,
        ENNReal.ofReal (C * ‖(G + (S * of A + c)ᴴ * (S * of A + c)).det‖⁻¹ ^ (card κ + card ι)) ≤
      ENNReal.ofReal (C * (‖S.det‖⁻¹ ^ (2 * card κ) * ‖G.det‖⁻¹ ^ card κ)) := by
  let g (v : ι → κ → ℂ) : ENNReal :=
    .ofReal (C * ‖(G + (of v)ᴴ * of v).det‖⁻¹ ^ (card κ + card ι))
  have h_det : Measurable fun v : ι → κ → ℂ ↦ (G + (of v)ᴴ * of v).det := by
    simpa using measurable_det_add_conjTranspose_mul (1 : Matrix ι ι ℂ) (0 : Matrix ι κ ℂ) G
  have hg : Measurable g := by fun_prop
  have h_rows (v : ι → κ → ℂ) : (of v)ᴴ * of v = ∑ i, vecMulVec (star (v i)) (v i) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]
  -- `hua_integral_le`, applied with the identity matrix and no shift, over all the rows
  have h_hua : ∫⁻ v, g v ≤ .ofReal (C * ‖G.det‖⁻¹ ^ card κ) := calc
    _ = (∫⋯∫⁻_Finset.univ, g) 0 := lintegral_eq_lmarginal_univ 0
    _ ≤ .ofReal (C * ((π ^ card κ / (card κ).factorial) ^ card ι * ‖G.det‖⁻¹ ^ card κ)) := by
      simpa [g, h_rows, add_comm (card κ)] using
        hua_integral_le 1 (by simp) 0 hG hC Finset.univ le_rfl 0
    _ ≤ _ := by grw [pi_pow_div_factorial_le_one hκ, one_pow, one_mul]
  calc
    _ = .ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ v, g v := lintegral_comp_mul_add hS c hg
    _ ≤ _ := by grw [h_hua, ← ENNReal.ofReal_mul (by positivity), mul_left_comm]

end HuaIntegral
