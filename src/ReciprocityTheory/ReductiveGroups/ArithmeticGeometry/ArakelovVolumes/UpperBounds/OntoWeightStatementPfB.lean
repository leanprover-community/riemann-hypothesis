import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

section V

variable {n : ℕ} {U : Set (V n)}

def twoLog {N M : ℕ} (a c : ℝ) (w : Fin N → V n → ℂ) (s : Fin M → V n → ℂ) (y : V n) : ℝ :=
  a * Real.log (∑ k, Complex.normSq (w k y)) + c * Real.log (∑ k, Complex.normSq (s k y))

theorem sumSq_cdAt {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun v => ∑ k, Complex.normSq (w k v)) y :=
  ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hw k) hy)

theorem twoLog_cdAt {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U) (a c : ℝ)
    {y : V n} (hy : y ∈ U) (hwp : 0 < ∑ k, Complex.normSq (w k y)) (hsp : 0 < ∑ k, Complex.normSq (s k y)) :
    ContDiffAt ℝ ∞ (twoLog a c w s) y := by
  unfold twoLog
  exact (contDiffAt_const.mul ((sumSq_cdAt hU hw hy).log hwp.ne')).add
    (contDiffAt_const.mul ((sumSq_cdAt hU hs hy).log hsp.ne'))

theorem logSum_levi_nonneg {N : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y))
    {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((Real.log (∑ k, Complex.normSq (w k v)) : ℝ) : ℂ)) y ξ).re :=
  lseV n N U (fun k v => Complex.normSq (w k v)) hU
    (fun k => Or.inr ⟨w k, ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).of_le HE.two_le_inf),
      fun _ _ => rfl⟩) hwp y hy ξ

theorem twoLog_levi_nonneg {N M : ℕ} (hU : IsOpen U) {w : Fin N → V n → ℂ} {s : Fin M → V n → ℂ}
    (hw : ∀ k, DifferentiableOn ℂ (w k) U) (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hwp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (w k y)) (hsp : ∀ y ∈ U, 0 < ∑ k, Complex.normSq (s k y))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {y : V n} (hy : y ∈ U) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun v => ((twoLog a c w s v : ℝ) : ℂ)) y ξ).re := by
  have h1 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (w k v))) y :=
    ((sumSq_cdAt hU hw hy).log (hwp y hy).ne').of_le HE.two_le_inf
  have h2 : ContDiffAt ℝ 2 (fun v => Real.log (∑ k, Complex.normSq (s k v))) y :=
    ((sumSq_cdAt hU hs hy).log (hsp y hy).ne').of_le HE.two_le_inf
  have e : (fun v => ((twoLog a c w s v : ℝ) : ℂ)) = fun v =>
      ((a * Real.log (∑ k, Complex.normSq (w k v)) + c * Real.log (∑ k, Complex.normSq (s k v)) : ℝ) : ℂ) := rfl
  rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h1, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have := logSum_levi_nonneg hU hw hwp hy ξ
  have := logSum_levi_nonneg hU hs hsp hy ξ
  positivity

end V

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem exp_neg_phla (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn : 0 < X.nfac la x := by
    unfold Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem pnorm_sq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x ^ 2 = Complex.normSq (P x) * Real.exp (-phla X la x) := by
  rw [pnorm_eq, mul_pow, exp_neg_phla X la hx, Complex.normSq_eq_norm_sq]

theorem sum_pnorm_sq {N : ℕ} (la : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∑ k, X.pnorm la (P k) x ^ 2 = (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X la x) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => pnorm_sq X la (P k) hx)

theorem phla_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la1 la2 : Wt X.Ψ r) (k : ℕ) :
    phla X (la1 + k • la2) x = phla X la1 x + k * phla X la2 x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

variable {X}

def PsK (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ :=
  phla X (Xa.Fp + Xa.T • Xa.L) x + (Xa.T : ℝ) * Real.log (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) +
    ((Xa.T : ℝ) - 1 / 2) * Real.log ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2)

theorem sumw_pos (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, Complex.normSq (Xa.w k x) := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  exact lt_of_lt_of_le (Complex.normSq_pos.2 hk)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Xa.w k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k))

theorem sums_pos {Xa : ArchInM X} (Fl : FlatM X Xa) {x : Frame X.Ψ r} {k0 : Fin (nd X)}
    (h : Fl.s k0 x ≠ 0) : 0 < ∑ k, Complex.normSq (Fl.s k x) :=
  lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (f := fun k => Complex.normSq (Fl.s k x)) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k0))

theorem PsK_eq (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    PsK Xa Fl x = phla X Xa.Fp x + ((1 / 2 : ℝ) * Real.log (∑ k, Complex.normSq (Xa.w k x)) +
      ((Xa.T : ℝ) - 1 / 2) * Real.log (∑ k, Complex.normSq (Fl.s k x))) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  unfold PsK
  rw [sum_pnorm_sq X _ _ hx, sum_pnorm_sq X _ _ hx, phla_add_nsmul X hx, mul_div_mul_right _ _ he.ne',
    Real.log_mul hw.ne' he.ne', Real.log_exp, Real.log_div hs.ne' hw.ne']
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem WSk_eq_exp (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    WSk X Xa Fl x = ENNReal.ofReal (Real.exp (-PsK Xa Fl x)) := by
  have hw := sumw_pos Xa hx
  have he : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hA : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]; positivity
  have hR : 0 < (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := div_pos hS hA
  unfold WSk
  rw [if_pos hx, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold PsK
  ring

def Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0}

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (k : Fin (nd X)) : DifferentiableOn ℂ (Fl.s k) X.dom :=
  (Fl.s_van k).1.1.1.1

theorem w_diffOn (Xa : ArchInM X) (k : Fin Xa.N) : DifferentiableOn ℂ (Xa.w k) X.dom :=
  (Xa.w_van k).1.1.1.1

theorem isOpen_Uk {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) :
    IsOpen (Uk Fl x0 k0) :=
  HE.isOpen_punct (ExF.isOpen_OmF X x0) (IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0)

theorem PsK_cpt_eventually {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) :
    (fun v => PsK Xa Fl (cpt X x0 v)) =ᶠ[𝓝 z] fun v => phla X Xa.Fp (cpt X x0 v) +
      twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v)) v := by
  filter_upwards [(isOpen_Uk Fl x0 k0).mem_nhds hz] with v hv
  rw [PsK_eq Xa Fl hv.1 (sums_pos Fl hv.2)]
  rfl

theorem twoLog_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (a c : ℝ) :
    ContDiffAt ℝ ∞ (twoLog a c (fun k v => Xa.w k (cpt X x0 v)) (fun k v => Fl.s k (cpt X x0 v))) z :=
  twoLog_cdAt (ExF.isOpen_OmF X x0) (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) x0)
    (fun k => IW.comp_cpt_diffOn X (s_diffOn Fl k) x0) a c hz.1 (sumw_pos Xa hz.1) (sums_pos Fl hz.2)

theorem PsK_cpt_cdAt {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X))
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) : ContDiffAt ℝ ∞ (fun v => PsK Xa Fl (cpt X x0 v)) z :=
  ((IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).add (twoLog_cpt_cdAt Fl x0 k0 hz _ _)).congr_of_eventuallyEq
    (PsK_cpt_eventually Fl x0 k0 hz)

theorem PsK_levi {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k0 : Fin (nd X)) (m : ℝ)
    (hm : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ Uk Fl x0 k0) (ξ : Fin (nd X) → ℂ) :
    m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
      (leviV (nd X) (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  have hT : (0 : ℝ) ≤ (Xa.T : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 1 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    linarith
  set tl := twoLog (1 / 2) ((Xa.T : ℝ) - 1 / 2) (fun k v => Xa.w k (cpt X x0 v))
    (fun k v => Fl.s k (cpt X x0 v)) with htl
  have hev : (fun w => ((PsK Xa Fl (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => (((phla X Xa.Fp (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) + tl w : ℝ) : ℂ) := by
    filter_upwards [PsK_cpt_eventually Fl x0 k0 hz] with w hw
    rw [hw]
    push_cast
    ring
  have h1 := (IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz.1).of_le HE.two_le_inf
  have h3 := (twoLog_cpt_cdAt Fl x0 k0 hz (1 / 2) ((Xa.T : ℝ) - 1 / 2)).of_le HE.two_le_inf
  have hU := isOpen_Uk Fl x0 k0
  have hpos : 0 ≤ (leviV (nd X) (fun v => ((tl v : ℝ) : ℂ)) z ξ).re :=
    twoLog_levi_nonneg hU (fun k => (IW.comp_cpt_diffOn X (w_diffOn Xa k) x0).mono fun v hv => hv.1)
      (fun k => (IW.comp_cpt_diffOn X (s_diffOn Fl k) x0).mono fun v hv => hv.1)
      (fun v hv => sumw_pos Xa hv.1) (fun v hv => sums_pos Fl hv.2) (by norm_num) hT hz ξ
  have hmz := hm z hz.1 ξ
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h2)) h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h2), Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hmz
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem sumP_contOn {N : ℕ} (L : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, ContinuousOn (P k) X.dom) :
    ContinuousOn (fun x => ∑ k, X.pnorm L (P k) x ^ 2) X.dom := by
  have hphl := IW.phla_contOn X L
  have hc : ContinuousOn (fun x => (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X L x)) X.dom :=
    (continuousOn_finsetSum _ fun k _ => Complex.continuous_normSq.comp_continuousOn (hP k)).mul
      (Real.continuous_exp.comp_continuousOn hphl.neg)
  exact hc.congr fun x hx => sum_pnorm_sq X L P hx

theorem WSk_meas (Xa : ArchInM X) (Fl : FlatM X Xa) : Measurable (WSk X Xa Fl) := by
  classical
  have hdo : IsOpen X.dom := IW.isOpen_dom X
  have hwc : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (Xa.w_van k).1.1.1.1.continuousOn
  have hsc : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (Fl.s_van k).1.1.1.1.continuousOn
  have hSw := sumP_contOn Xa.L Xa.w hwc
  have hSs := sumP_contOn Xa.L Fl.s hsc
  have hSw0 : ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≠ 0 := fun x hx => by
    rw [sum_pnorm_sq X _ _ hx]
    exact (mul_pos (sumw_pos Xa hx) (Real.exp_pos _)).ne'
  have h1 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0) :=
    ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (IW.phla_contOn X _).neg))
      continuousOn_const hdo.measurableSet
  have h2 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn hSw)
      continuousOn_const hdo.measurableSet
  have h3 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
        ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn
        (hSs.div hSw hSw0))
      continuousOn_const hdo.measurableSet
  have key : WSk X Xa Fl = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
          ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0 := by
    funext x
    by_cases hx : x ∈ X.dom
    · simp only [WSk, if_pos hx, Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp only [WSk, if_neg hx, Pi.mul_apply, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply,
        zero_mul]
  rw [key]
  exact (h1.mul h2).mul h3

theorem pnorm_lact (L : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm L P (lact γ x) = X.pnorm L P x := by
  rw [pnorm_eq X, pnorm_eq X, hP.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X L hγ, one_mul,
    normFactor_leftAction_holds r X L γ hγ x hx]

theorem phla_lact (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phla X la (lact γ x) = phla X la x := by
  unfold phla
  rw [normFactor_leftAction_holds r X la γ hγ x hx]

theorem WSk_metric (Xa : ArchInM X) (Fl : FlatM X Xa) :
    IsMetricW X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  refine ⟨WSk_meas Xa Fl, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb := OntoS.dom_rmul X hx hb
    have hbc : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2 := by
      have := OntoE.bchar_ne X (Xa.Fp + Xa.T • Xa.L) hb
      positivity
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hwS k) hx hb
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hsS k) hx hb
    simp only [WSk, if_pos hxb, if_pos hx, hpw, hps]
    rw [IW.exp_neg_phla_rmul X normFactor_rightBorel_holds _ hx hb, ENNReal.ofReal_div_of_pos hbc]
    simp only [div_eq_mul_inv]
    ring
  · have hxg := OntoS.dom_lact X hγ hx
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      pnorm_lact Xa.L (hwS k) hγ hx
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      pnorm_lact Xa.L (hsS k) hγ hx
    simp only [WSk, if_pos hxg, if_pos hx, hpw, hps, phla_lact _ hγ hx]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem nfac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_nonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x := by
  rw [pnorm_eq X]
  exact mul_nonneg (norm_nonneg _) (nfac_nonneg la x)

theorem WSk_lower (Xa : ArchInM X) (Fl : FlatM X Xa) :
    WLower X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hT1 : (1 : ℝ) ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    exact_mod_cast (by nlinarith : 1 ≤ Xa.T)
  choose Cw hCw using fun k => (Xa.w_van k).1.1.2
  choose Cs hCs using fun k => (Fl.s_van k).1.1.2
  set u : ℝ := (Xa.T : ℝ) - 1 / 2 with hu
  have hu0 : 0 < u := by linarith
  set Mw : ℝ := ∑ k, max (Cw k) 0 ^ 2 + 1 with hMw
  set Ms : ℝ := ∑ k, max (Cs k) 0 ^ 2 + 1 with hMs
  have hMw0 : 0 < Mw := by positivity
  have hMs0 : 0 < Ms := by positivity
  refine ⟨Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹, by positivity, fun x hx => ?_⟩
  have hSwM : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Mw := by
    have : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ ∑ k, max (Cw k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCw k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSsM : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ Ms := by
    have : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ ∑ k, max (Cs k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCs k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSw : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]
    exact mul_pos (sumw_pos Xa hx) (Real.exp_pos _)
  have hSs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  set Sw := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hSwd
  set Ss := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSsd
  set e := Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) with he
  have he0 : 0 < e := Real.exp_pos _
  simp only [WSk, if_pos hx]
  rw [← hSwd, ← hSsd, ← he]
  rcases hSs0.eq_or_lt with hS | hS
  · rw [← hS, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top]
    · exact le_top
    · exact mul_ne_zero (ENNReal.ofReal_pos.mpr he0).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hSw) ENNReal.ofReal_ne_top).ne'
  · rw [ENNReal.ofReal_rpow_of_pos hSw, ENNReal.ofReal_rpow_of_pos (div_pos hS hSw),
      ← ENNReal.ofReal_mul he0.le, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have eq : Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) = Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ := by
      have hsplit : Sw ^ u = Sw ^ (Xa.T : ℝ) * Sw ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hSw]
        congr 1
      rw [Real.rpow_neg hSw.le, Real.rpow_neg (div_pos hS hSw).le, Real.div_rpow hS.le hSw.le,
        inv_div, hsplit]
      have h1 : 0 < Sw ^ (Xa.T : ℝ) := Real.rpow_pos_of_pos hSw _
      have h2 : 0 < Ss ^ u := Real.rpow_pos_of_pos hS _
      field_simp
    have hA : Mw ^ (-(1 / 2 : ℝ)) ≤ Sw ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hSw hSwM (by norm_num)
    have hB : (Ms ^ u)⁻¹ ≤ (Ss ^ u)⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hS _) (Real.rpow_le_rpow hS.le hSsM hu0.le)
    have hC : Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ :=
      mul_le_mul hA hB (by positivity) (by positivity)
    calc Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ * e ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ * e :=
          mul_le_mul_of_nonneg_right hC he0.le
      _ = e * Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) := by rw [mul_assoc e, eq]; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
end
