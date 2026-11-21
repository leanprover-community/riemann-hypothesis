import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepA
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

theorem bsB_holo_ratio (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {la : La} {a b : ι → Y → ℂ}
    (ha : A.IsSecOn la (A.Mset w0 s De) a) (hb : A.IsSecOn la (A.Mset w0 s De) b)
    (hb0 : ∀ y ∈ A.Mset w0 s De, b (A.pick y) y ≠ 0) :
    Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => a (A.pick (y : Y)) y / b (A.pick (y : Y)) y) := by
  rw [holo_flat_iff A hD hF (fun y => a (A.pick y) y / b (A.pick y) y)]
  intro i
  have hne : ∀ v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De,
      (b i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
    bsA_ne_of_tr A hb.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hb0 _ hv.2)
  have h3 := (ha.1 i).mul ((hb.1 i).inv hne)
  refine h3.congr fun v hv => ?_
  simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply]
  rw [← div_eq_mul_inv]
  exact bsA_tr_ratio A ha.2 hb.2 hv.2 (A.mem_pick _) ((A.chart i).map_target hv.1)

theorem bsB_z_ne {x : Y} (hx : x ∈ A.Mset w0 s De) {i0 : Fin n}
    (hX : MvPolynomial.X i0 ∣ De) : A.zmap w0 s x i0 ≠ 0 := by
  obtain ⟨Q, hQ⟩ := hX
  intro h0
  apply hx.2
  rw [hQ, MvPolynomial.eval_mul, MvPolynomial.eval_X, h0, zero_mul]

theorem bsB_lambda (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      Real.log (∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2)) := by
  have hg : ∀ k, Holo n (flatStein A hD hF).z
      (fun y : A.Mset w0 s De => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y) := fun k =>
    bsB_holo_ratio A hD hF (bsA_isSecOn_mono A (hD.sec_w k) (Set.subset_univ _))
      (bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ _)) fun y hy => hy.1
  have hpos : ∀ x : A.Mset w0 s De, 0 < ∑ i : Fin 0, Real.exp ((Fin.elim0 i : A.Mset w0 s De → ℝ) x) +
      ∑ k, ‖w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2 := by
    intro x
    obtain ⟨k, hk⟩ := hD.no_common_zero x
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x ≠ 0 := div_ne_zero hk x.2.1
    positivity
  have h := hLSE (A.Mset w0 s De) (flatStein A hD hF).z (flatStein A hD hF).isLocalHomeomorph 0 N
    (fun i => Fin.elim0 i) (fun k y => w k (A.pick (y : Y)) y / w0 (A.pick (y : Y)) y)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hg hpos
  simpa using h

section Psi

variable {mu0 : La} {σ : ι → Y → ℂ}

def bsPsi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  -Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
    Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2)

def bsPsiC (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (i : ι) (y : Y) : ℝ :=
  A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2) +
    Real.log (‖(jz A w0 s i y).det‖ ^ 2)

theorem bsB_logsq {f : V n → ℂ} {p : V n} {O : Set (V n)} (hO : IsOpen O) (hp : p ∈ O)
    (hf : DifferentiableOn ℂ f O) (hne : f p ≠ 0) :
    ContDiffAt ℝ ∞ (fun v => Real.log (‖f v‖ ^ 2)) p := by
  have h1 : ContDiffAt ℂ ∞ f p :=
    (contDiffOn_of_differentiableOn n f O hO hf p hp).contDiffAt (hO.mem_nhds hp)
  have h2 : ContDiffAt ℝ ∞ (fun v => ‖f v‖ ^ 2) p := (h1.restrict_scalars ℝ).norm_sq ℂ
  exact h2.log (by positivity)

theorem bsB_psi_chart (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {y : Y} (hy : y ∈ A.Mset w0 s De) {i : ι}
    (hi : y ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ y = bsPsiC A w0 s mu0 σ i y := by
  have hp := A.mem_pick y
  have hσi : σ i y ≠ 0 := bsA_ne_of_tr A hσ.1.2 hy hi hp (hσ.2 y hy)
  have hg : A.g A.kap (A.pick y) i y ≠ 0 := A.g_ne _ _ _ y hp hi
  have hdet : (jz A w0 s i y).det ≠ 0 := jz_det_ne A hD hF y hy i hi
  unfold bsPsi bsPsiC
  rw [bsA_nsq_chart A hσ.1.2 hy hi, jz_det_trans A hD hF y hy (A.pick y) i hp hi,
    bsA_ph_sub A mu0 A.kap hi, A.ph_trans A.kap (A.pick y) i y hp hi]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, norm_mul, mul_pow,
    Real.log_mul (by positivity) (by positivity), norm_inv, inv_pow, Real.log_inv]
  ring

theorem bsB_O_open (hD : A.D0 L w w0 s) (i : ι) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) :=
  (A.chart i).isOpen_inter_preimage_symm (isOpen_Mset A hD)

theorem bsB_O_mem {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De :=
  ⟨(A.chart i).map_source hi, by simpa [(A.chart i).left_inv hi] using hx⟩

theorem bsB_jz_eq {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    jz A w0 s i ((A.chart i).symm v) = fderiv ℂ (A.zLoc w0 s i) v := by
  unfold jz; rw [(A.chart i).right_inv hv]

theorem bsB_det_diff (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {x : Y}
    (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      DifferentiableAt ℂ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v := by
  filter_upwards [differentiableAt_det_jz A hD hF x hx i hi,
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v h1 h2
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(A.chart i).open_target.mem_nhds h2] with v' hv'
  simp [bsB_jz_eq A hv']

theorem bsB_inv_diffOn (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (i : ι) :
    DifferentiableOn ℂ ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  have h := (hσ.1.1 i).inv (fun v hv =>
    bsA_ne_of_tr A hσ.1.2 hv.2 ((A.chart i).map_target hv.1) (A.mem_pick _) (hσ.2 _ hv.2))
  exact h.congr fun v _ => rfl

theorem bsB_psiC_smooth (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.ph (mu0 - A.kap) i ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i x) ∧
    ContDiffAt ℝ ∞ ((fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) := by
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  refine ⟨(A.smooth_ph _ i).contDiffAt ((A.chart i).open_target.mem_nhds hxO.1), ?_, ?_⟩
  · have hne : ((fun y => (σ i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact inv_ne_zero (bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx))
    exact bsB_logsq hO hxO (bsB_inv_diffOn A hσ i) hne
  · have hc : ContDiffAt ℂ ∞ ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) := by
      refine (contDiffAt_det_jz A hD hF x hx i hi).congr_of_eventuallyEq ?_
      filter_upwards [(A.chart i).open_target.mem_nhds hxO.1] with v hv
      simp [bsB_jz_eq A hv]
    have h2 : ContDiffAt ℝ ∞ (fun v => ‖((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) v‖ ^ 2)
        (A.chart i x) := (hc.restrict_scalars ℝ).norm_sq ℂ
    have hne : ((fun y => (jz A w0 s i y).det) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
      exact jz_det_ne A hD hF x hx i hi
    exact h2.log (by positivity)

end Psi

section Ph0

variable {mu0 : La} {σ : ι → Y → ℂ}

theorem bsB_psi_evEq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) : bsPsi A w0 s mu0 σ =ᶠ[𝓝 x] bsPsiC A w0 s mu0 σ i := by
  filter_upwards [(isOpen_Mset A hD).mem_nhds hx, (A.chart i).open_source.mem_nhds hi]
    with y h1 h2
  exact bsB_psi_chart A hD hF hσ h1 h2

theorem bsB_psi_smoothAt (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι}
    (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (bsPsi A w0 s mu0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hC : ContDiffAt ℝ ∞ (bsPsiC A w0 s mu0 σ i ∘ (A.chart i).symm) (A.chart i x) :=
    (h1.add h2).add h3
  refine hC.congr_of_eventuallyEq ?_
  have ht : Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := (A.chart i).continuousAt_symm ((A.chart i).map_source hi)
    rwa [ContinuousAt, (A.chart i).left_inv hi] at this
  exact (bsB_psi_evEq A hD hF hσ hx hi).comp_tendsto ht

theorem bsB_psi_levi (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    {x : Y} (hx : x ∈ A.Mset w0 s De) {i : ι} (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    0 ≤ A.leviAt i (bsPsi A w0 s mu0 σ) x ξ := by
  obtain ⟨h1, h2, h3⟩ := bsB_psiC_smooth A hD hF hσ hx hi
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hO := bsB_O_open A (De := De) hD i
  have hxO := bsB_O_mem A hx hi
  rw [leviAt_congr A i _ _ x hi (bsB_psi_evEq A hD hF hσ hx hi)]
  have e1 : bsPsiC A w0 s mu0 σ i = fun y => (fun y => A.ph (mu0 - A.kap) i y +
      Real.log (‖(σ i y)⁻¹‖ ^ 2)) y + Real.log (‖(jz A w0 s i y).det‖ ^ 2) := rfl
  have E1 := leviAt_add A i (fun y => A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2))
    (fun y => Real.log (‖(jz A w0 s i y).det‖ ^ 2)) x ((h1.add h2).of_le hle) (h3.of_le hle) ξ
  have E2 := leviAt_add A i (A.ph (mu0 - A.kap) i) (fun y => Real.log (‖(σ i y)⁻¹‖ ^ 2)) x
    (h1.of_le hle) (h2.of_le hle) ξ
  have hσx : σ i x ≠ 0 := bsA_ne_of_tr A hσ.1.2 hx hi (A.mem_pick x) (hσ.2 x hx)
  have E3 := leviAt_log_normSq A i (fun y => (σ i y)⁻¹) x hi (by
      filter_upwards [hO.mem_nhds hxO] with v hv
      exact (bsB_inv_diffOn A hσ i).differentiableAt (hO.mem_nhds hv)) (inv_ne_zero hσx) ξ
  have E4 := leviAt_log_normSq A i (fun y => (jz A w0 s i y).det) x hi (bsB_det_diff A hD hF hx hi)
      (jz_det_ne A hD hF x hx i hi) ξ
  have E5 := hpos i x hi ξ
  simp only [add_zero] at E5
  rw [e1]
  beta_reduce at E1 E2 E3 E4 ⊢
  linarith

def bsPh0 (A : WeightedAtlas n Y ι La) (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (mu0 : La) (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  bsPsi A w0 s mu0 σ y + 1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)

theorem smooth_leviNonneg_frameWeight (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hLSE : LSEAll.{u} n)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0)) :
    SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) ∧
    LeviNonneg n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPh0 A w w0 s mu0 σ x) := by
  obtain ⟨hΛs, hΛl⟩ := bsB_lambda A hD hF hLSE
  have hΨs : SmoothR n (flatStein A hD hF).z (fun x : A.Mset w0 s De => bsPsi A w0 s mu0 σ x) :=
    smoothR_flat A hD hF _ fun x hx =>
      ⟨A.pick x, A.mem_pick x, bsB_psi_smoothAt A hD hF hσ hx (A.mem_pick x)⟩
  have hΨl : LeviNonneg n (flatStein A hD hF).z
      (fun x : A.Mset w0 s De => bsPsi A w0 s mu0 σ x) :=
    leviNonneg_flat A hD hF _ fun x hx =>
      ⟨A.pick x, A.mem_pick x, bsB_psi_smoothAt A hD hF hσ hx (A.mem_pick x),
        bsB_psi_levi A hD hF hσ hpos hx (A.mem_pick x)⟩
  have hcs : SmoothR n (flatStein A hD hF).z (fun _ : A.Mset w0 s De => (1 / 2 : ℝ)) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.const n _ ((1 / 2 : ℝ) : ℂ)
  have hHs := SmoothR.mul n _ _ _ hcs hΛs
  refine ⟨SmoothR.add n _ _ _ hΨs hHs, fun x ξ => ?_⟩
  have e := levi_add n (flatStein A hD hF).z _ _ (SmoothR.ckR n _ 2 _ hΨs)
    (SmoothR.ckR n _ 2 _ hHs) x ξ
  have e2 := levi_const_mul n (flatStein A hD hF).z (1 / 2) _ (SmoothR.ckR n _ 2 _ hΛs) x ξ
  unfold bsPh0
  rw [e, Complex.add_re, e2, Complex.re_ofReal_mul]
  have h1 := hΨl x ξ
  have h2 := hΛl x ξ
  positivity

end Ph0

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem bsC_nsq_contOn {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : A.IsSecOn la U a)
    (hU : IsOpen U) : ContinuousOn (A.nsq la a) U := by
  intro y hy
  set i := A.pick y
  have hsrc : (A.chart i).source ∩ U ∈ 𝓝 y :=
    ((A.chart i).open_source.inter hU).mem_nhds ⟨A.mem_pick y, hy⟩
  have h1 : ContinuousOn (a i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (ha.1 i).continuousOn
  have h2 : ContinuousOn (a i) ((A.chart i).source ∩ U) := by
    have := h1.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
      (fun x (hx : x ∈ (A.chart i).source ∩ U) => ⟨(A.chart i).map_source hx.1, by simpa [(A.chart i).left_inv hx.1] using hx.2⟩)
    exact this.congr fun x hx => by simp [(A.chart i).left_inv hx.1]
  have hc : ContinuousAt (fun x => ‖a i x‖ ^ 2 * Real.exp (-A.ph la i x)) y := by
    have h3 := h2.continuousAt hsrc
    have h4 := (bsA_ph_cont A la i).continuousAt
      ((A.chart i).open_source.mem_nhds (A.mem_pick y))
    exact (h3.norm.pow 2).mul (h4.neg.rexp)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hsrc] with x hx
  exact (bsA_nsq_chart A ha.2 hx.2 hx.1).symm

theorem bsC_nsq_prod (la L : La) (m : ℕ) (q u v : ι → Y → ℂ) (c : ℂ) (y : Y)
    (hq : q (A.pick y) y = c * (u (A.pick y) y * v (A.pick y) y ^ m)) :
    A.nsq (la + m • L) q y = ‖c‖ ^ 2 * A.nsq la u y * A.nsq L v y ^ m := by
  unfold nsq
  rw [hq, A.ph_add la (m • L) _ y (A.mem_pick y), bsA_ph_nsmul A L m (A.mem_pick y)]
  rw [norm_mul, norm_mul, norm_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, neg_add,
    Real.exp_add, show -((m : ℝ) * A.ph L (A.pick y) y) = (m : ℝ) * (-A.ph L (A.pick y) y) by ring,
    Real.exp_nat_mul, ← pow_mul]
  ring

theorem bsC_sqn_ratio {N : ℕ} (la : La) (u : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (y : Y)
    (h0 : w0 (A.pick y) y ≠ 0) :
    A.sqn la u y = A.nsq la w0 y * ∑ k, ‖u k (A.pick y) y / w0 (A.pick y) y‖ ^ 2 := by
  unfold sqn nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ‖w0 (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [norm_div, div_pow]
  field_simp

theorem bsC_alg (Fn nσ a Z S ρ : ℝ) (m : ℕ) (ha : 0 < a) (hZ : 0 < Z) (hS : 0 < S) :
    Fn * nσ * a ^ m * (a * Z) ^ (-((m : ℝ) - 1 / 2)) * (a * S) ^ (-(1 / 2 : ℝ)) * ρ =
      Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) := by
  rw [Real.mul_rpow ha.le hZ.le, Real.mul_rpow ha.le hS.le]
  have key : a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha, ← Real.rpow_add ha]
    ring_nf; exact Real.rpow_zero a
  calc Fn * nσ * a ^ m * (a ^ (-((m : ℝ) - 1 / 2)) * Z ^ (-((m : ℝ) - 1 / 2))) *
        (a ^ (-(1 / 2 : ℝ)) * S ^ (-(1 / 2 : ℝ))) * ρ
      = Fn * Z ^ (-((m : ℝ) - 1 / 2)) * (nσ * ρ * S ^ (-(1 / 2 : ℝ))) *
          (a ^ m * a ^ (-((m : ℝ) - 1 / 2)) * a ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [key, mul_one]

theorem exp_neg_frameWeight_eq {N : ℕ} (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (mu0 : La) (σ : ι → Y → ℂ) (y : Y) (hσ : 0 < A.nsq mu0 σ y)
    (hd : (jz A w0 s (A.pick y) y).det ≠ 0)
    (hS : 0 < ∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) :
    Real.exp (-bsPh0 A w w0 s mu0 σ y) =
      A.nsq mu0 σ y * (Real.exp (A.ph A.kap (A.pick y) y) / ‖(jz A w0 s (A.pick y) y).det‖ ^ 2) *
        (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  unfold bsPh0 bsPsi
  have hd2 : 0 < ‖(jz A w0 s (A.pick y) y).det‖ ^ 2 := by positivity
  rw [Real.rpow_def_of_pos hS]
  rw [show -(-Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
      Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
      1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)) =
      Real.log (A.nsq mu0 σ y) + A.ph A.kap (A.pick y) y -
        Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2) +
        Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2) * (-(1 / 2 : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hσ, Real.exp_log hd2]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

theorem bsD_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (x : Y) (hx : x ∈ A.Mset w0 s De) :
    0 < A.nsq L w0 x ∧ 0 < A.nsq mu0 σ x ∧
      0 < ∑ k, ‖s k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      0 < ∑ k, ‖w k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      (jz A w0 s (A.pick x) x).det ≠ 0 := by
  obtain ⟨i0, hX0⟩ := hX
  refine ⟨bsA_nsq_pos A hx.1, bsA_nsq_pos A (hσ.2 x hx), ?_, ?_,
    jz_det_ne A hD hF x hx _ (A.mem_pick x)⟩
  · have h := bsB_z_ne A hx hX0
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i0))
    have : s i0 (A.pick x) x / w0 (A.pick x) x ≠ 0 := h
    positivity
  · obtain ⟨k, hk⟩ := hD.no_common_zero x
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick x) x / w0 (A.pick x) x ≠ 0 := div_ne_zero hk hx.1
    positivity

theorem bsD_denom (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (fun i y => σ i y * w0 i y ^ m) := by
  have hw := bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ (A.Mset w0 s De))
  refine ⟨fun i => ?_, ?_⟩
  · have h := (hσ.1.1 i).mul ((hw.1 i).pow m)
    refine h.congr fun v _ => ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  · intro i j y hy hi hj
    have h := bsA_tr_mul A hσ.1.2 (bsA_tr_pow A hw.2 m) i j y hy hi hj
    simpa only using h

theorem bsD_heq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (f : ι → Y → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + T' • L) f x * A.sqn L s x ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w x ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2 + 1)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by
  obtain ⟨ha, hnσ, hZ, hSw, hd⟩ := bsD_pos A hD hF hσ hX x x.2
  have hb : σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T' ≠ 0 :=
    mul_ne_zero (hσ.2 x x.2) (pow_ne_zero _ x.2.1)
  have e1 := bsC_nsq_prod A mu0 L T' f σ w0
    (f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')) x
    (div_mul_cancel₀ _ hb).symm
  have e2 := bsC_sqn_ratio A L s w0 x x.2.1
  have e3 := bsC_sqn_ratio A L w w0 x x.2.1
  have e4 := exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw
  have hs0 : 0 ≤ A.sqn L s x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x
  have hw0 : 0 ≤ A.sqn L w x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x
  have hp : 0 ≤ A.nsq (mu0 + T' • L) f x * A.sqn L s x ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w x ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (bsA_nsq_nonneg A _ f x) (Real.rpow_nonneg hs0 _))
      (Real.rpow_nonneg hw0 _)
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  rw [e1, e2, e3, e4, show (T' : ℝ) - 3 / 2 + 1 = (T' : ℝ) - 1 / 2 by ring]
  exact bsC_alg _ _ _ _ _ _ T' ha hZ hSw

theorem bsD_hfin (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ x, ENNReal.ofReal
      (‖f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')‖ ^ 2 *
        (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2 + 1)) *
        Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤ := by
  have hφm : Measurable fun y => ENNReal.ofReal (A.nsq (mu0 + T' • L) f y *
      A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (((bsA_nsq_cont A hf).measurable.mul
      ((bsA_sqn_cont A hD.sec_s).measurable.pow_const _)).mul
      ((bsA_sqn_cont A hD.sec_w).measurable.pow_const _))
  have hflat := lintegral_flat A hD hF _ hφm
  have hc := lintegral_congr (μ := vol n (flatStein A hD hF).z) (bsD_heq A hD hF hσ hX T' f)
  rw [← hc, ← hflat]
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hint

theorem bsD_skoda (hS : SAll.{u} n) (hLSE : LSEAll.{u} n) (hn : 2 ≤ n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → A.Mset w0 s De → ℂ, (∀ k, Holo n (flatStein A hD hF).z (hh k)) ∧
      (∀ x : A.Mset w0 s De, f (A.pick (x : Y)) x /
          (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T') =
        ∑ k, s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x * hh k x) ∧
      ∫⁻ x, ENNReal.ofReal ((∑ k, ‖hh k x‖ ^ 2) *
          (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤ := by
  obtain ⟨hph0s, hph0l⟩ := smooth_leviNonneg_frameWeight A hD hF hLSE hσ hpos
  have hw0M := bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ (A.Mset w0 s De))
  have hg : ∀ k, Holo n (flatStein A hD hF).z
      (fun x : A.Mset w0 s De => s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x) := fun k =>
    bsB_holo_ratio A hD hF (a := s k) (b := w0) (bsA_isSecOn_mono A (hD.sec_s k) (Set.subset_univ _))
      hw0M fun y hy => hy.1
  have hnz : ∀ x : A.Mset w0 s De, ∃ k, s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x ≠ 0 := by
    intro x
    obtain ⟨i0, hX0⟩ := hX
    exact ⟨i0, bsB_z_ne A x.2 hX0⟩
  have ht : (n : ℝ) - 1 < (T' : ℝ) - 3 / 2 := by
    have : ((n + 1 : ℕ) : ℝ) ≤ T' := by exact_mod_cast hT
    push_cast at this; linarith
  have hFz : Holo n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')) :=
    bsB_holo_ratio A hD hF (la := mu0 + T' • L) (a := f) (b := fun i y => σ i y * w0 i y ^ T')
      (bsA_isSecOn_mono A hf (Set.subset_univ _))
      (bsD_denom A hD hσ T') fun y hy => mul_ne_zero (hσ.2 y hy) (pow_ne_zero _ hy.1)
  have hfin := bsD_hfin A hD hF hσ hX T' f hf hint
  have hSk : SStatement n (A.Mset w0 s De) := hS (A.Mset w0 s De)
  obtain ⟨hh, h1, h2, h3⟩ := hSk (flatStein A hD hF) n
    (fun k (x : A.Mset w0 s De) => s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x)
    (fun x => bsPh0 A w w0 s mu0 σ x) ((T' : ℝ) - 3 / 2)
    (fun x => f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T'))
    hn hg hnz hph0s hph0l ht hFz hfin
  exact ⟨hh, h1, h2, lt_of_le_of_lt h3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

open Classical in

def bsExt (M : Set Y) (h : M → ℂ) (y : Y) : ℂ := if hy : y ∈ M then h ⟨y, hy⟩ else 0

def bsH (M : Set Y) (h : M → ℂ) (σ w0 : ι → Y → ℂ) (m : ℕ) (i : ι) (y : Y) : ℂ :=
  bsExt M h y * (σ i y * w0 i y ^ m)

def bsW (A : WeightedAtlas n Y ι La) (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (T' : ℕ) (y : Y) : ℝ :=
  A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))

theorem bsE_ext_mem {M : Set Y} (h : M → ℂ) {y : Y} (hy : y ∈ M) : bsExt M h y = h ⟨y, hy⟩ := by
  unfold bsExt; rw [dif_pos hy]

theorem bsE_sec (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (h : A.Mset w0 s De → ℂ)
    (hh : Holo n (flatStein A hD hF).z h) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (bsH (A.Mset w0 s De) h σ w0 m) := by
  have hb := bsD_denom A hD hσ m
  have hh' : Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) := by
    have : (fun y : A.Mset w0 s De => bsExt (A.Mset w0 s De) h y) = h :=
      funext fun y => bsE_ext_mem h y.2
    rw [this]; exact hh
  have hd := (holo_flat_iff A hD hF _).mp hh'
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have := (hd i).mul (hb.1 i)
    refine this.congr fun v _ => ?_
    simp [bsH]
  · simp only [bsH]
    have := hb.2 i j y hy hi hj
    simp only at this
    rw [this]; ring

theorem bsE_heq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (h : A.Mset w0 s De → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖h x‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by
  obtain ⟨ha, hnσ, hZ, hSw, hd⟩ := bsD_pos A hD hF hσ hX x x.2
  have e1 := bsC_nsq_prod A mu0 L (T' - 1) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) σ w0 (h x) x
    (by simp only [bsH]; rw [bsE_ext_mem h x.2])
  have e2 := bsC_sqn_ratio A L s w0 x x.2.1
  have e3 := bsC_sqn_ratio A L w w0 x x.2.1
  have e4 := exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw
  have hs0 : 0 ≤ A.sqn L s x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x
  have hw0 : 0 ≤ A.sqn L w x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x
  have hp : 0 ≤ A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
      bsW A L w s T' x :=
    mul_nonneg (bsA_nsq_nonneg A _ _ x)
      (mul_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg hw0 _))
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  have hc : ((T' - 1 : ℕ) : ℝ) - 1 / 2 = (T' : ℝ) - 3 / 2 := by
    rw [Nat.cast_sub hT]; push_cast; ring
  unfold bsW
  rw [e1, e2, e3, e4, ← hc, ← mul_assoc]
  exact bsC_alg _ _ _ _ _ _ (T' - 1) ha hZ hSw

theorem bsE_sqn_s_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    {x : Y} (hx : x ∈ A.Mset w0 s De) : 0 < A.sqn L s x := by
  obtain ⟨ha, -, hZ, -, -⟩ := bsD_pos A hD hF hσ hX x hx
  rw [bsC_sqn_ratio A L s w0 x hx.1]; positivity

open Classical in
theorem bsE_meas (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h) :
    Measurable ((A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y * bsW A L w s T' y))
      (fun _ => 0)) := by
  have hMo := isOpen_Mset A (De := De) hD
  have h1 := bsC_nsq_contOn A (bsE_sec A hD hF hσ h hh (T' - 1)) hMo
  have h2 : ContinuousOn (bsW A L w s T') (A.Mset w0 s De) := by
    unfold bsW
    refine ContinuousOn.mul ?_ ?_
    · exact (bsA_sqn_cont A hD.sec_s).continuousOn.rpow_const fun x hx =>
        Or.inl (bsE_sqn_s_pos A hD hF hσ hX hx).ne'
    · exact (bsA_sqn_cont A hD.sec_w).continuousOn.rpow_const fun x _ =>
        Or.inl (bsA_sqn_pos A (hD.no_common_zero x)).ne'
  exact ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn (h1.mul h2)) continuousOn_const hMo.measurableSet

open Classical in
theorem bsE_int (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 1 ≤ T') (hh : Fin n → A.Mset w0 s De → ℂ)
    (hhol : ∀ k, Holo n (flatStein A hD hF).z (hh k)) (k : Fin n)
    (hbd : ∫⁻ x, ENNReal.ofReal ((∑ j, ‖hh j x‖ ^ 2) *
          (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤) :
    ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) (hh k) σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤ := by
  rw [lintegral_flat A hD hF _ (bsE_meas A hD hF hσ hX T' (hh k) (hhol k))]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hbd
  rw [Set.piecewise_eq_of_mem _ _ _ x.2, bsE_heq A hD hF hσ hX T' hT (hh k) x]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖hh k x‖ ^ 2 ≤ ∑ j, ‖hh j x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ k)
  have h2 : 0 ≤ (∑ j, ‖s j (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^
      (-((T' : ℝ) - 3 / 2)) := Real.rpow_nonneg (by positivity) _
  have h3 := Real.exp_pos (-bsPh0 A w w0 s mu0 σ x)
  gcongr

open Classical in
theorem bsE_loc (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (hT : 2 ≤ T') (h : A.Mset w0 s De → ℂ) (hh : Holo n (flatStein A hD hF).z h)
    (hint : ∫⁻ y in A.Mset w0 s De, (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) y ∂A.mu < ⊤) (y : Y) :
    ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu < ⊤ := by
  obtain ⟨C, hC⟩ := hD.s_le_w
  have hMo := isOpen_Mset A (De := De) hD
  set C' := max C 1 with hC'
  set K := A.sqn L w y + 1 with hK
  have hK0 : 0 < K := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => bsA_nsq_nonneg A L (w k) y
    simp only [sqn] at hK ⊢; linarith
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hp : 0 ≤ (T' : ℝ) - 3 / 2 := by
    have : (2 : ℝ) ≤ T' := by exact_mod_cast hT
    linarith
  set c := (C' * K) ^ (-((T' : ℝ) - 3 / 2)) * K ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hK0 _)
  set U := {y' | A.sqn L w y' < K} with hU
  have hUo : IsOpen U := isOpen_lt (bsA_sqn_cont A hD.sec_w) continuous_const
  have hyU : y ∈ U := by simp [hU, hK]
  refine ⟨U, hUo.mem_nhds hyU, ?_⟩
  set ψ := (A.Mset w0 s De).piecewise (fun y => ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) y *
        bsW A L w s T' y)) (fun _ => 0) with hψ
  have hbound : ∀ x ∈ U ∩ A.Mset w0 s De, ENNReal.ofReal
      (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ≤
      ENNReal.ofReal c⁻¹ * ψ x := by
    intro x hx
    rw [hψ, Set.piecewise_eq_of_mem _ _ _ hx.2, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs := bsE_sqn_s_pos A hD hF hσ hX hx.2
    have hw := bsA_sqn_pos A (la := L) (hD.no_common_zero x) (w := w)
    have hwK : A.sqn L w x ≤ K := le_of_lt hx.1
    have hsK : A.sqn L s x ≤ C' * K := by
      calc A.sqn L s x ≤ C * A.sqn L w x := hC x
        _ ≤ C' * A.sqn L w x := mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le
        _ ≤ C' * K := mul_le_mul_of_nonneg_left hwK (by positivity)
    have hW : c ≤ bsW A L w s T' x := by
      unfold bsW
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hs hsK (by linarith))
        (Real.rpow_le_rpow_of_nonpos hw hwK (by norm_num)) (Real.rpow_pos_of_pos hK0 _).le
        (Real.rpow_nonneg hs.le _)
    have hn0 := bsA_nsq_nonneg A (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
    calc A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x
        = c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x * c) := by
          field_simp
      _ ≤ c⁻¹ * (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x *
          bsW A L w s T' x) := by gcongr
  calc ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal
        (A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) h σ w0 (T' - 1)) x) ∂A.mu
      ≤ ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        setLIntegral_mono' (hUo.inter hMo).measurableSet hbound
    _ ≤ ∫⁻ x in A.Mset w0 s De, ENNReal.ofReal c⁻¹ * ψ x ∂A.mu :=
        lintegral_mono_set Set.inter_subset_right
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x in A.Mset w0 s De, ψ x ∂A.mu :=
        lintegral_const_mul _ (bsE_meas A hD hF hσ hX T' h hh)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem b_step {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
    (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) (hLSE : LSEAll.{u} n)
    (hn : 2 ≤ n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → ι → Y → ℂ,
      (∀ k, A.IsSec (mu0 + (T' - 1) • L) (hh k) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (hh k) y *
          A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ k, s k i y * hh k i y := by
  classical
  have hT1 : 1 ≤ T' := by omega
  have hT2 : 2 ≤ T' := by omega
  have hMo := isOpen_Mset A (De := De) hD
  obtain ⟨H, hHol, hid, hbd⟩ := bsD_skoda A hS hLSE hn hD hF hX hσ hpos T' hT f hf hint
  have hint' := fun k => bsE_int A hD hF hσ hX T' hT1 H hHol k hbd
  have hex : ∀ k, ∃ G : ι → Y → ℂ, A.IsSec (mu0 + (T' - 1) • L) G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source →
        G i y = bsH (A.Mset w0 s De) (H k) σ w0 (T' - 1) i y := fun k =>
    ext_Mset A hE hD hF _ _ (bsE_sec A hD hF hσ (H k) (hHol k) (T' - 1))
      (bsE_loc A hD hF hσ hX T' hT2 (H k) (hHol k) (hint' k))
  choose G hGs hGeq using hex
  refine ⟨G, fun k => ⟨hGs k, ?_⟩, ?_⟩
  · have hae : ∀ᵐ y ∂A.mu, y ∈ A.Mset w0 s De := by
      rw [ae_iff]; exact mu_compl_Mset A hN hD hF
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    refine lt_of_eq_of_lt (setLIntegral_congr_fun hMo.measurableSet fun y hy => ?_) (hint' k)
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    have : A.nsq (mu0 + (T' - 1) • L) (G k) y =
        A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) (H k) σ w0 (T' - 1)) y := by
      unfold nsq; rw [hGeq k (A.pick y) y hy (A.mem_pick y)]
    rw [this, mul_assoc]
    rfl
  · intro i y hy
    have hcont : ContinuousOn (fun y => ∑ k, s k i y * G k i y) (A.chart i).source :=
      continuousOn_finsetSum _ fun k _ =>
        (continuousOn_section_chart A (hD.sec_s k) i).mul (continuousOn_section_chart A (hGs k) i)
    have hEq : Set.EqOn (f i) (fun y => ∑ k, s k i y * G k i y)
        ((A.chart i).source ∩ A.Mset w0 s De) := by
      intro x hx
      have hxM := hx.2
      have hp := A.mem_pick x
      have hw : w0 i x ≠ 0 := denominator_ne_zero_on_chart A hD hxM hx.1
      have hσi : σ i x ≠ 0 := bsA_ne_of_tr A hσ.1.2 hxM hx.1 hp (hσ.2 x hxM)
      have hfM := bsA_isSecOn_mono A hf (Set.subset_univ (A.Mset w0 s De))
      have hr1 : f i x / (σ i x * w0 i x ^ T') =
          f (A.pick x) x / (σ (A.pick x) x * w0 (A.pick x) x ^ T') :=
        bsA_tr_ratio A hfM.2 (bsD_denom A hD hσ T').2 hxM hx.1 hp
      have hr2 : ∀ k, s k (A.pick x) x / w0 (A.pick x) x = s k i x / w0 i x := fun k =>
        (bsA_tr_ratio A (bsA_isSecOn_mono A (hD.sec_s k) (Set.subset_univ _)).2
          (bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ _)).2 hxM hx.1 hp).symm
      have hid' := hid ⟨x, hxM⟩
      simp only at hid'
      rw [← hr1] at hid'
      simp_rw [hr2] at hid'
      have hG : ∀ k, G k i x = H k ⟨x, hxM⟩ * (σ i x * w0 i x ^ (T' - 1)) := by
        intro k
        rw [hGeq k i x hxM hx.1]
        simp only [bsH, bsE_ext_mem _ hxM]
      have hpow : w0 i x ^ T' = w0 i x ^ (T' - 1) * w0 i x := by
        rw [← pow_succ, Nat.sub_add_cancel hT1]
      have hb : σ i x * w0 i x ^ T' ≠ 0 := mul_ne_zero hσi (pow_ne_zero _ hw)
      have e : f i x = (∑ k, s k i x / w0 i x * H k ⟨x, hxM⟩) * (σ i x * w0 i x ^ T') := by
        rw [← hid', div_mul_cancel₀ _ hb]
      simp only
      rw [e, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hG k, hpow]
      field_simp
    exact hEq.of_subset_closure (continuousOn_section_chart A hf i) hcont Set.inter_subset_left
      ((dense_Mset A hD hF).open_subset_closure_inter (A.chart i).open_source) hy

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem real_bound {d F Ssq Wsq C1 B2 c m6 : ℝ} {T n : ℕ} (hnT' : n < T) (hd : 0 ≤ d)
    (hF0 : 0 ≤ F) (hF : F ≤ (C1 * d ^ (T - n)) ^ 2 * B2) (hB2 : 0 ≤ B2) (hc : 0 < c)
    (hS : c * d ^ 2 ≤ Ssq) (hm : 0 < m6) (hW : m6 ≤ Wsq) :
    F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ)) ≤
      (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
        d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
  have hnT : n ≤ T := hnT'.le
  have hK : 0 ≤ C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) := by positivity
  rcases hd.eq_or_lt with h0 | hdpos
  · subst h0
    have hz : (0:ℝ) ^ (T - n) = 0 := zero_pow (by omega)
    rw [hz, mul_zero] at hF
    have hF' : F = 0 := le_antisymm (by simpa using hF) hF0
    rw [hF', zero_mul, zero_mul]
    positivity
  · have hSpos : 0 < Ssq := lt_of_lt_of_le (by positivity) hS
    have h1 : Ssq ^ (-((T : ℝ) - 1 / 2)) ≤ (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by
        have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
        linarith)
    have h2 : Wsq ^ (-(1 / 2 : ℝ)) ≤ m6 ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hm hW (by norm_num)
    calc F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ))
        ≤ ((C1 * d ^ (T - n)) ^ 2 * B2) * (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) *
            m6 ^ (-(1 / 2 : ℝ)) := by
          have hW0 : 0 ≤ Wsq ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (hm.le.trans hW) _
          have hS0 : 0 ≤ Ssq ^ (-((T : ℝ) - 1 / 2)) := Real.rpow_nonneg hSpos.le _
          gcongr
      _ = (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
            d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
          have e1 : (d ^ (T - n)) ^ 2 = d ^ (2 * ((T : ℝ) - n)) := by
            rw [← pow_mul, ← Real.rpow_natCast]
            congr 1
            push_cast [Nat.cast_sub hnT]
            ring
          have e2 : (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) =
              c ^ (-((T : ℝ) - 1 / 2)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) := by
            rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hd]
            push_cast
            ring_nf
          have e3 : d ^ (2 * ((T : ℝ) - n)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) =
              d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
            rw [← Real.rpow_add hdpos]; ring_nf
          rw [mul_pow, e1, e2]
          rw [← e3]
          ring

theorem sqn_s_eq (A : WeightedAtlas n Y ι La) {L : La} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) {i : ι} {x : Y} (hx : x ∈ (A.chart i).source)
    (hw : w0 i x ≠ 0) :
    A.sqn L s x = ‖w0 i x‖ ^ 2 * Real.exp (-A.ph L i x) * ‖A.zLoc w0 s i (A.chart i x)‖ ^ 2 := by
  unfold sqn
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [A.nsq_eq_chart (hs k) hx]
  simp only [zLoc, PiLp.toLp_apply, (A.chart i).left_inv hx, norm_div, div_pow]
  have : ‖w0 i x‖ ^ 2 ≠ 0 := by positivity
  field_simp

theorem zLoc_lower (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hn : 1 ≤ n) {P : Y}
    (hP : P ∈ A.zeroSet s) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v in 𝓝 (A.chart (A.pick P) P),
      ‖v - A.chart (A.pick P) P‖ ≤ K * ‖A.zLoc w0 s (A.pick P) v‖ := by
  set i := A.pick P
  set vP := A.chart i P
  set zL := A.zLoc w0 s i
  have hdet : (fderiv ℂ zL vP).det ≠ 0 := hD.coord P hP
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdiff : DifferentiableAt ℂ zL vP := by
    by_contra h
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt h]
    show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin]
    exact zero_pow (by omega)
  have hz0 : zL vP = 0 := by
    ext k
    simp only [zL, zLoc, PiLp.toLp_apply, vP, (A.chart i).left_inv (A.mem_pick P)]
    rw [hP k]; simp
  set D := fderiv ℂ zL vP
  set E := (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ u, ‖u‖ ≤ K0 * ‖D u‖ := by
    refine ⟨‖(E.symm : V n →L[ℂ] V n)‖, fun u => ?_⟩
    have h := E.antilipschitz.le_mul_dist u 0
    simp only [dist_zero_right, map_zero] at h
    exact h
  set K1 := max K0 1
  have hK1 : 0 < K1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlo := hdiff.hasFDerivAt.isLittleO
  have hev := hlo.def (show (0:ℝ) < 1 / (2 * K1) by positivity)
  refine ⟨2 * K1, by positivity, ?_⟩
  filter_upwards [hev] with v hv
  rw [hz0, sub_zero] at hv
  have h1 : ‖v - vP‖ ≤ K1 * ‖D (v - vP)‖ :=
    (hK0 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖D (v - vP)‖ ≤ ‖zL v‖ + ‖zL v - D (v - vP)‖ := by
    have := norm_sub_le (zL v) (zL v - D (v - vP))
    rwa [sub_sub_cancel] at this
  have h3 : K1 * (1 / (2 * K1) * ‖v - vP‖) = ‖v - vP‖ / 2 := by field_simp
  nlinarith [norm_nonneg (zL v - D (v - vP)), norm_nonneg (zL v)]

theorem local_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T) {P : Y} (hP : P ∈ A.zeroSet s) (hv : A.VanishOrd f P (T - n)) :
    ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧
      ∫⁻ y in U, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  set i := A.pick P with hi
  set e := A.chart i with he
  set vP := e P with hvP
  have hPs : P ∈ e.source := A.mem_pick P
  have hvt : vP ∈ e.target := e.map_source hPs
  have htn : e.target ∈ 𝓝 vP := e.open_target.mem_nhds hvt
  have hsymm : ContinuousAt e.symm vP := e.continuousAt_symm hvt
  have hsP : e.symm vP = P := e.left_inv hPs
  have cph : ∀ la' : La, ContinuousAt (fun v => A.ph la' i (e.symm v)) vP := fun la' =>
    (A.smooth_ph la' i).continuousOn.continuousAt htn
  have cw0 : ContinuousAt (fun v => w0 i (e.symm v)) vP := by
    have h := (hD.isSection_denom.1 i).continuousOn
    simp only [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt htn
  obtain ⟨C1, hC1⟩ := hv
  obtain ⟨K3, hK3pos, hK3⟩ := A.zLoc_lower hD (by omega) hP
  set B2 := Real.exp (-A.ph la i P) + 1 with hB2
  have hE2 : ∀ᶠ v in 𝓝 vP, Real.exp (-A.ph la i (e.symm v)) < B2 := by
    have hc : ContinuousAt (fun v => Real.exp (-A.ph la i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph la).neg
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  set g4 : V n → ℝ := fun v => ‖w0 i (e.symm v)‖ ^ 2 * Real.exp (-A.ph L i (e.symm v)) with hg4
  have g4P : 0 < g4 vP := by
    simp only [g4, hsP]
    have := hD.w0_ne P hP
    positivity
  have hE4 : ∀ᶠ v in 𝓝 vP, g4 vP / 2 < g4 v :=
    ((cw0.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp (cph L).neg)).eventually
      (eventually_gt_nhds (half_lt_self g4P))
  set g6 : V n → ℝ := fun v => A.sqn L w (e.symm v) with hg6
  have g6P : 0 < g6 vP := by
    simp only [g6, hsP]
    obtain ⟨k, hk⟩ := hD.no_common_zero P
    have h0 : 0 < A.nsq L (w k) P := by
      unfold nsq
      have := norm_pos_iff.2 hk
      positivity
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq L (w j) P)
      (fun j _ => A.nsq_nonneg L (w j) P) (Finset.mem_univ k))
  have hE6 : ∀ᶠ v in 𝓝 vP, g6 vP / 2 < g6 v :=
    ((A.continuous_sqn hD.sec_w).continuousAt.comp hsymm).eventually
      (eventually_gt_nhds (half_lt_self g6P))
  set B7 := Real.exp (A.ph A.kap i P) + 1 with hB7
  have hE7 : ∀ᶠ v in 𝓝 vP, Real.exp (A.ph A.kap i (e.symm v)) < B7 := by
    have hc : ContinuousAt (fun v => Real.exp (A.ph A.kap i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph A.kap)
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ v in 𝓝 vP, v ∈ e.target from htn).and (hC1.and (hE2.and (hK3.and (hE4.and (hE6.and hE7))))))
  set r := min ε 1 with hr
  set W := Metric.ball vP r with hW
  have hWb : W ⊆ Metric.ball vP ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWt : W ⊆ e.target := fun v hv => (hball v (hWb hv)).1
  have hUo : IsOpen (e.source ∩ e ⁻¹' W) := e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨e.source ∩ e ⁻¹' W, hUo, ⟨hPs, Metric.mem_ball_self (lt_min hε one_pos)⟩, ?_⟩
  set c := (g4 vP / 2) / K3 ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set m6 := g6 vP / 2 with hm6
  have hm6pos : 0 < m6 := by positivity
  set K := C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) with hK
  have hB2pos : 0 < B2 := by positivity
  have hKnn : 0 ≤ K := by positivity
  set ψ : V n → ℝ≥0∞ := fun v => ENNReal.ofReal ‖v - vP‖ ^ (-2 * ((n : ℝ) - 1 / 2)) with hψ
  have hψc : Continuous ψ :=
    ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hpt : ∀ x ∈ e.source ∩ e ⁻¹' W,
      ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w x ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal K * ψ (e x) := by
    rintro x ⟨hxs, hxW⟩
    obtain ⟨-, h1, h2, h3, h4, h6, -⟩ := hball (e x) (hWb hxW)
    have hx : e.symm (e x) = x := e.left_inv hxs
    simp only [g4, g6, hx] at h4 h6
    rw [hx] at h1 h2
    set d := ‖e x - vP‖ with hd
    have hw0 : w0 i x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h4
      have : g4 vP / 2 < 0 := by simpa using h4
      linarith
    have hS : c * d ^ 2 ≤ A.sqn L s x := by
      rw [A.sqn_s_eq hD.sec_s hxs hw0]
      set z := ‖A.zLoc w0 s i (e x)‖
      have hz : d ^ 2 ≤ K3 ^ 2 * z ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hc1 : c * d ^ 2 ≤ (g4 vP / 2) * z ^ 2 := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [g4P]
      exact hc1.trans (mul_le_mul_of_nonneg_right h4.le (sq_nonneg _))
    have hF : A.nsq la f x ≤ (C1 * d ^ (T - n)) ^ 2 * B2 := by
      rw [A.nsq_eq_chart hf hxs]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2.le (Real.exp_pos _).le
        (sq_nonneg _)
    have hR := real_bound (T := T) (n := n) (by omega) (norm_nonneg _) (A.nsq_nonneg la f x) hF
      hB2pos.le hcpos hS hm6pos h6.le
    calc ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
          A.sqn L w x ^ (-(1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (K * d ^ (-2 * ((n : ℝ) - 1 / 2))) := ENNReal.ofReal_le_ofReal hR
      _ = ENNReal.ofReal K * ENNReal.ofReal (d ^ (-2 * ((n : ℝ) - 1 / 2))) :=
          ENNReal.ofReal_mul hKnn
      _ ≤ ENNReal.ofReal K * ψ (e x) := by
          gcongr
          rcases (norm_nonneg (e x - vP)).eq_or_lt with h0 | hpos
          · rw [← hd] at h0
            rw [← h0, Real.zero_rpow (by
              have : (2:ℝ) ≤ n := by exact_mod_cast hn
              linarith)]
            simp
          · simp only [ψ]
            rw [ENNReal.ofReal_rpow_of_pos hpos]
  have hUm : MeasurableSet (e.source ∩ e ⁻¹' W) := hUo.measurableSet
  calc ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq la f y *
        A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
      ≤ ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal K * ψ (e y) ∂A.mu :=
        setLIntegral_mono' hUm hpt
    _ = ENNReal.ofReal K * ∫⁻ y in e.source ∩ e ⁻¹' W, ψ (e y) ∂A.mu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal B7 * ∫⁻ v in W, ψ v) := by
        gcongr
        exact A.lintegral_chart_le i P Metric.isOpen_ball hWt _
          (fun v hv => ENNReal.ofReal_le_ofReal (hball v (hWb hv)).2.2.2.2.2.2.le) ψ hψc
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
        exact lintegral_ball_rpow_lt_top hMVI (by omega) vP (min_le_right _ _) (by linarith)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem sqn_pos_of_ne (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {y : Y} (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  have h0 : 0 < A.nsq la (w k) y := by
    unfold nsq
    have := norm_pos_iff.2 hk
    positivity
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq la (w j) y)
    (fun j _ => A.nsq_nonneg la (w j) y) (Finset.mem_univ k))

theorem sqn_pos_of_notMem (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    {y : Y} (h : y ∉ A.zeroSet s) : 0 < A.sqn la s y := by
  apply A.sqn_pos_of_ne
  simpa [zeroSet] using h

theorem setLIntegral_biUnion_le {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset κ) (U : κ → Set α) (G : α → ℝ≥0∞) :
    ∫⁻ y in ⋃ P ∈ F, U P, G y ∂μ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂μ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem start_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu < ⊤)
    (hvan : ∀ P ∈ A.zeroSet s, A.VanishOrd f P (T - n)) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  classical
  set G : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) with hG
  have hloc : ∀ P ∈ A.zeroSet s, ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∫⁻ y in U, G y ∂A.mu < ⊤ :=
    fun P hP => A.local_int hMVI hn hD hf hT hP (hvan P hP)
  choose! U hUo hPU hUint using hloc
  set F := hD.finite_S.toFinset
  set V := ⋃ P ∈ F, U P with hV
  have hVo : IsOpen V := isOpen_biUnion (fun P hP => hUo P ((Set.Finite.mem_toFinset _).1 hP))
  have hSV : A.zeroSet s ⊆ V := fun P hP =>
    Set.mem_biUnion ((Set.Finite.mem_toFinset _).2 hP) (hPU P hP)
  obtain ⟨C, hC⟩ := hD.family_le_coords V hVo hSV
  set a : ℝ := (T : ℝ) - 1 / 2 with ha
  have hpt : ∀ y ∈ Vᶜ, G y ≤ ENNReal.ofReal (C ^ a) *
      ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
    intro y hy
    have hyS : y ∉ A.zeroSet s := fun h => hy (hSV h)
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y hy
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have h1 : A.sqn L s y ^ (-a) ≤ (A.sqn L w y / C) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [div_le_iff₀ hCpos]; linarith)
        (by have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
            linarith)
    have h2 : (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) =
        C ^ a * A.sqn L w y ^ (-(T : ℝ)) := by
      rw [Real.div_rpow hw.le hCpos.le, Real.rpow_neg hCpos.le, div_inv_eq_mul, mul_comm _ (C ^ a),
        mul_assoc, ← Real.rpow_add hw]
      congr 2
      ring
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la f y
    calc A.nsq la f y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))
        ≤ A.nsq la f y * (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) := by
          have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
          gcongr
      _ = C ^ a * (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
          rw [mul_assoc, h2]; ring
  calc ∫⁻ y, G y ∂A.mu = ∫⁻ y in V ∪ Vᶜ, G y ∂A.mu := by
        rw [Set.union_compl_self, Measure.restrict_univ]
    _ ≤ ∫⁻ y in V, G y ∂A.mu + ∫⁻ y in Vᶜ, G y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y in Vᶜ, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add (setLIntegral_biUnion_le _ _ _ _) (setLIntegral_mono' hVo.measurableSet.compl hpt)
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 (fun P hP => hUint P
          ((Set.Finite.mem_toFinset _).1 hP)), ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint⟩

theorem end_int (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {h : ι → Y → ℂ}
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-((n : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu < ⊤ := by
  have : NullSingletonClass A.mu := ⟨fun x => A.mu_singleton hn x⟩
  have hS0 : A.mu (A.zeroSet s) = 0 := hD.finite_S.measure_zero A.mu
  obtain ⟨C, hC⟩ := hD.s_le_w
  set a : ℝ := (n : ℝ) - 1 / 2 with ha
  have hae : ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ≤
      ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with y hyS
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have hna : 0 ≤ a := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : (C * A.sqn L w y) ^ (-a) ≤ A.sqn L s y ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hs hCy (by linarith)
    have h2 : A.sqn L w y ^ (-(n : ℝ)) =
        C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
      rw [Real.mul_rpow hCpos.le hw.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hCpos,
        mul_assoc, ← Real.rpow_add hw]
      have e1 : a + -a = 0 := by ring
      have e2 : -a + -(1 / 2 : ℝ) = -(n : ℝ) := by rw [ha]; ring
      rw [e1, e2, Real.rpow_zero, one_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la h y
    have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
    have := Real.rpow_nonneg hCpos.le a
    rw [h2]
    calc A.nsq la h y * (C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))))
        = C ^ a * (A.nsq la h y * (C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          ring
      _ ≤ C ^ a * (A.nsq la h y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          gcongr
  calc ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu
      ≤ ∫⁻ y, ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu := lintegral_mono_ae hae
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

theorem sum_int (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (hh : ∀ q ∈ F, A.IsSec la (h q)) (Wt : Y → ℝ) (hWt : Measurable Wt)
    (hW0 : ∀ y, 0 ≤ Wt y)
    (hint : ∀ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ∂A.mu < ⊤ := by
  have hpt : ∀ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ≤
      ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) := by
    intro y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (A.nsq_nonneg _ _ _) (hW0 y)),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.nsq_sum_le la F h y) (hW0 y)
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (F.card : ℝ) *
        ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := lintegral_mono hpt
    _ = ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro q hq
        exact (ENNReal.measurable_ofReal.comp
          ((A.continuous_nsq (hh q hq)).measurable.mul hWt)).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 hint)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem b (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n)
    (hLSE : LSEAll.{u} n) (hMVI : MVIntStatement n) : BStatement n Y ι La := by
  classical
  intro A L mu0 N w w0 s De σ T f hn hD hF hX hσ hpos hT hf hint hvan
  have h0 := A.start_int hMVI hn hD hf hT hint hvan
  have key : ∀ m, m ≤ T - n → ∃ hh : (Fin m → Fin n) → ι → Y → ℂ,
      (∀ q, A.IsSec (mu0 + (T - m) • L) (hh q) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T - m) • L) (hh q) y *
          A.sqn L s y ^ (-(((T - m : ℕ) : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
            < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ q, (∏ j, s (q j) i y) * hh q i y := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => f, fun q => ⟨by simpa using hf, by simpa using h0⟩, fun i y _ => ?_⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨hh, hhP, hsum⟩ := ih (by omega)
      have hT' : n + 1 ≤ T - m := by omega
      choose H hH hHsum using fun q =>
        b_step A hS hE hN hLSE hn hD hF hX hσ hpos (T - m) hT' (hh q) (hhP q).1 (hhP q).2
      refine ⟨fun q' => H (Fin.tail q') (q' 0), fun q' => ?_, ?_⟩
      · have e1 : T - (m + 1) = T - m - 1 := by omega
        have e2 : (((T - m - 1 : ℕ) : ℝ) - 1 / 2) = ((T - m : ℕ) : ℝ) - 3 / 2 := by
          rw [Nat.cast_sub (show 1 ≤ T - m by omega)]
          push_cast
          ring
        obtain ⟨h1, h2⟩ := hH (Fin.tail q') (q' 0)
        rw [e1, e2]
        exact ⟨h1, h2⟩
      · intro i y hy
        rw [hsum i y hy, ← (Fin.consEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hHsum q i y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have et : Fin.tail ((Fin.consEquiv fun _ => Fin n) (k, q)) = q :=
          Fin.tail_cons (α := fun _ => Fin n) k q
        rw [et]
        ring
  obtain ⟨hh, hhP, hsum⟩ := key (T - n) le_rfl
  have eT : T - (T - n) = n := by omega
  rw [eT] at hhP
  set cnt : (Fin (T - n) → Fin n) → Fin n → ℕ :=
    fun q k => (Finset.univ.filter (fun j => q j = k)).card with hcnt
  refine ⟨fun α i y => ∑ q ∈ Finset.univ.filter (fun q => cnt q = α), hh q i y,
    fun α _ => ⟨?_, ?_⟩, ?_⟩
  · exact A.isSec_sum _ (fun q _ => (hhP q).1)
  · exact A.sum_int _ hh (fun q _ => (hhP q).1) (fun y => A.sqn L w y ^ (-(n : ℝ)))
      ((A.continuous_sqn hD.sec_w).measurable.pow_const _)
      (fun y => Real.rpow_nonneg (A.sqn_nonneg _ _ y) _)
      (fun q _ => A.end_int (by omega) hD (hhP q).2)
  · intro i y hy
    rw [hsum i y hy]
    have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin (T - n) → Fin n)),
        cnt q ∈ Finset.Nat.antidiagonalTuple n (T - n) := by
      intro q _
      rw [Finset.Nat.mem_antidiagonalTuple]
      simp only [cnt]
      rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (q j))]
      simp
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq' : cnt q = α := (Finset.mem_filter.1 hq).2
    congr 1
    rw [← hq', ← Finset.prod_fiberwise Finset.univ q (fun j => s (q j) i y)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.prod_const]

end

end ReciprocityTheory.L2DbarEstimates.Y
end
