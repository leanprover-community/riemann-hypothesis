import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatValEqValAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar

section Parts

variable {D : ℕ} {O : Set (V D)} {u χ : V D → ℝ}

theorem continuous_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ O) : Continuous fun v => u v * χ v :=
  (hu.mul hχ.continuousOn).continuous_of_tsupport_subset hO (tsupport_mul_subset_right.trans hs)

theorem integrable_mul_of_tsupport (hO : IsOpen O) (hu : ContinuousOn u O) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) : Integrable fun v => u v * χ v :=
  (continuous_mul_of_tsupport hO hu hχ hs).integrable_of_hasCompactSupport hc.mul_left

theorem contDiffOn_fderiv_apply (hO : IsOpen O) {n : ℕ∞ω} (hu : ContDiffOn ℝ (n + 1) u O) (a : V D) :
    ContDiffOn ℝ n (fun v => fderiv ℝ u v a) O :=
  (hu.fderiv_of_isOpen hO le_rfl).clm_apply contDiffOn_const

theorem integral_mul_fderiv_of_tsupport (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ χ v a = -∫ v, fderiv ℝ u v a * χ v :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 0) hu a).continuousOn
      hχ.continuous hc hs)
    (integrable_mul_of_tsupport hO hu.continuousOn
      ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ a)
      ((tsupport_fderiv_apply_subset ℝ a).trans hs))
    (integrable_mul_of_tsupport hO hu.continuousOn hχ.continuous hc hs)
    (fun _ hv => (hu.contDiffAt (hO.mem_nhds (hs hv))).differentiableAt one_ne_zero)
    (fun v _ => hχ.differentiable one_ne_zero v)

theorem fderiv_fderiv_apply {v : V D} (hu : ContDiffAt ℝ 2 u v) (a : V D) :
    fderiv ℝ (fun w => fderiv ℝ u w a) v a = fderiv ℝ (fderiv ℝ u) v a a := by
  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    (differentiableAt_const _)]
  simp

theorem continuousOn_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (a : V D) :
    ContinuousOn (fun v => fderiv ℝ (fderiv ℝ u) v a a) O :=
  (contDiffOn_fderiv_apply hO (n := 0) (contDiffOn_fderiv_apply hO (n := 1) hu a) a).continuousOn.congr
    fun _ hv => (fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv)) a).symm

theorem integral_mul_fderiv_fderiv (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (a : V D) :
    ∫ v, u v * fderiv ℝ (fderiv ℝ χ) v a a = ∫ v, fderiv ℝ (fderiv ℝ u) v a a * χ v := by
  have hχ' : ContDiff ℝ 1 fun v => fderiv ℝ χ v a :=
    contDiffOn_univ.1 (contDiffOn_fderiv_apply isOpen_univ (n := 1) hχ.contDiffOn a)
  have h₁ := integral_mul_fderiv_of_tsupport hO (hu.of_le one_le_two) hχ' (hc.fderiv_apply ℝ a)
    ((tsupport_fderiv_apply_subset ℝ a).trans hs) a
  have h₂ := integral_mul_fderiv_of_tsupport hO (contDiffOn_fderiv_apply hO (n := 1) hu a)
    (hχ.of_le one_le_two) hc hs a
  simp only [fderiv_fderiv_apply hχ.contDiffAt] at h₁
  rw [h₁, h₂, neg_neg]
  refine integral_congr_ae (.of_forall fun v => ?_)
  by_cases hv : v ∈ O
  · simp only [fderiv_fderiv_apply (hu.contDiffAt (hO.mem_nhds hv))]
  · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero]

theorem exists_leviV_re_eq (ξ : Fin D → ℂ) : ∃ a b : V D, ∀ (f : V D → ℝ) (v : V D),
    ContDiffAt ℝ 2 f v → (leviV D (fun w => (f w : ℂ)) v ξ).re =
      4⁻¹ * (fderiv ℝ (fderiv ℝ f) v a a + fderiv ℝ (fderiv ℝ f) v b b) :=
  ⟨_, _, fun _ _ hf => by rw [← LocalMaximumSecondDerivative.leviV_re_eq hf ξ]; ring⟩

theorem continuousOn_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) (ξ : Fin D → ℂ) :
    ContinuousOn (fun v => (leviV D (fun w => (u w : ℂ)) v ξ).re) O :=
  have ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  (continuousOn_const.mul ((continuousOn_fderiv_fderiv hO hu a).add
    (continuousOn_fderiv_fderiv hO hu b))).congr fun v hv => h u v (hu.contDiffAt (hO.mem_nhds hv))

theorem integral_mul_leviV_re (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O) (ξ : Fin D → ℂ) :
    ∫ v, u v * (leviV D (fun w => (χ w : ℂ)) v ξ).re =
      ∫ v, (leviV D (fun w => (u w : ℂ)) v ξ).re * χ v := by
  obtain ⟨a, b, h⟩ := exists_leviV_re_eq ξ
  have I₁ (c : V D) : Integrable fun v => u v * fderiv ℝ (fderiv ℝ χ) v c c := by
    simp only [← fderiv_fderiv_apply hχ.contDiffAt]
    refine integrable_mul_of_tsupport hO hu.continuousOn ?_ ((hc.fderiv_apply ℝ c).fderiv_apply ℝ c)
      ((tsupport_fderiv_apply_subset ℝ c).trans ((tsupport_fderiv_apply_subset ℝ c).trans hs))
    simp only [fderiv_fderiv_apply hχ.contDiffAt]
    exact continuousOn_univ.1 (continuousOn_fderiv_fderiv isOpen_univ hχ.contDiffOn c)
  have I₂ (c : V D) : Integrable fun v => fderiv ℝ (fderiv ℝ u) v c c * χ v :=
    integrable_mul_of_tsupport hO (continuousOn_fderiv_fderiv hO hu c) hχ.continuous hc hs
  calc _ = ∫ v, 4⁻¹ * (u v * fderiv ℝ (fderiv ℝ χ) v a a + u v * fderiv ℝ (fderiv ℝ χ) v b b) :=
        integral_congr_ae (.of_forall fun v => by simp only [h χ v hχ.contDiffAt]; ring)
    _ = ∫ v, 4⁻¹ * (fderiv ℝ (fderiv ℝ u) v a a * χ v + fderiv ℝ (fderiv ℝ u) v b b * χ v) := by
        rw [integral_const_mul, integral_const_mul, integral_add (I₁ a) (I₁ b),
          integral_add (I₂ a) (I₂ b), integral_mul_fderiv_fderiv hO hu hχ hc hs,
          integral_mul_fderiv_fderiv hO hu hχ hc hs]
    _ = _ := by
        refine integral_congr_ae (.of_forall fun v => ?_)
        by_cases hv : v ∈ O
        · simp only [h u v (hu.contDiffAt (hO.mem_nhds hv))]; ring
        · simp only [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), mul_zero, add_zero]

theorem nonneg_of_integral_mul_nonneg (hO : IsOpen O) (hu : ContinuousOn u O)
    (h : ∀ χ : V D → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      (∀ v, 0 ≤ χ v) → 0 ≤ ∫ v, u v * χ v) {v : V D} (hv : v ∈ O) : 0 ≤ u v := by
  by_contra hlt
  rw [not_le] at hlt
  have hn : O ∩ {w | u w < 0} ∈ 𝓝 v := inter_mem (hO.mem_nhds hv)
    ((hu.continuousAt (hO.mem_nhds hv)).eventually_lt continuousAt_const hlt)
  obtain ⟨χ, hs, hc, hχ, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hn
  have h0 (w) : 0 ≤ χ w := (hr ⟨w, rfl⟩).1
  have hs' := hs.trans inter_subset_left
  have hp : 0 < ∫ w, -u w * χ w :=
    (continuous_mul_of_tsupport hO hu.neg hχ.continuous hs').integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := v) hc.mul_left (fun w => by
        by_cases hw : w ∈ tsupport χ
        · exact mul_nonneg (neg_nonneg.2 (le_of_lt (hs hw).2)) (h0 w)
        · simp [image_eq_zero_of_notMem_tsupport hw]) (by simp [h1, hlt.ne])
  simp only [neg_mul, integral_neg] at hp
  linarith [h χ hχ hc hs' h0]

theorem posCurrent_iff_leviV (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O) :
    PosCurrent O u ↔ ∀ v ∈ O, ∀ ξ, 0 ≤ (leviV D (fun w => (u w : ℂ)) v ξ).re := by
  have h2 {χ : V D → ℝ} (h : ContDiff ℝ ∞ χ) : ContDiff ℝ 2 χ := h.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨fun h v hv ξ => nonneg_of_integral_mul_nonneg hO (continuousOn_leviV_re hO hu ξ)
    (fun χ h₁ h₂ h₃ h₄ => (h.2 χ h₁ h₂ h₃ h₄ ξ).trans_eq (integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ)) hv,
    fun h => ⟨hu.continuousOn.locallyIntegrableOn hO.measurableSet, fun χ h₁ h₂ h₃ h₄ ξ => ?_⟩⟩
  rw [integral_mul_leviV_re hO hu (h2 h₁) h₂ h₃ ξ]
  refine integral_nonneg fun v => ?_
  by_cases hv : v ∈ O
  · exact mul_nonneg (h v hv ξ) (h₄ v)
  · simp [image_eq_zero_of_notMem_tsupport fun h => hv (h₃ h)]

end Parts

namespace Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {ψ : Y.pts σ → ℝ}

theorem mSmooth.mPsh_iff_levi (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ) :
    mPsh Y σ Δ m ψ ↔ ∀ (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ), y ∈ c.e.source →
      y ∈ eqnSet σ Δ g → ∀ ξ, 0 ≤ c.levi (fun z => m.wt g z + ψ z) y ξ := by
  refine forall₂_congr fun c g => ?_
  have ho : IsOpen (chartDom c Δ g) := isOpen_over _ (isOpen_eqnSet Δ g)
  have hs : (Y.an σ).SmoothOn (eqnSet σ Δ g) fun z => m.wt g z + ψ z := fun j =>
    ((h.2 g).mono (fun _ hz => ⟨trivial, hz⟩) j).add (hψ.mono (subset_univ _) j)
  rw [and_iff_right (.of_forall fun _ _ => h.1 trivial)]
  refine (posCurrent_iff_leviV ho ((hs.chart (isOpen_eqnSet Δ g) c).of_le
    (WithTop.coe_le_coe.2 le_top))).trans ⟨fun H y hy hg => H _ (mem_over _ hy hg), fun H v hv ξ => ?_⟩
  have := H _ (c.e.map_target hv.1) hv.2 ξ
  rwa [AlgChart.levi, c.e.right_inv hv.1] at this

theorem mSmooth.levi_frame (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    {c : AlgChart Y.str σ Y.dim} {g g' : Y.Fnˣ} {y : Y.pts σ} (hy : y ∈ c.e.source)
    (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g') (ξ : Fin Y.dim → ℂ) :
    c.levi (fun z => m.wt g' z + ψ z) y ξ = c.levi (fun z => m.wt g z + ψ z) y ξ :=
  AnRead.levi_eq_of_add_log (R := Y.an σ) (f := fun z => m.wt g z + ψ z)
    ((isOpen_eqnSet Δ g).inter (isOpen_eqnSet Δ g'))
    (fun j => ((h.2 g).mono (fun _ hz => ⟨trivial, hz.1⟩) j).add (hψ.mono (subset_univ _) j))
    (holoOn_tv Δ g g') (fun _ hz => tv_ne_zero hz.1 hz.2)
    (fun z hz => by rw [Met.wt_trans (h.1 trivial) hz.1 hz.2]; ring) hy ⟨hg, hg'⟩ ξ

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem mSmooth.mPsh_iff_semiPos (h : mSmooth Y σ Δ m) (hψ : (Y.an σ).SmoothOn univ ψ)
    (hp : Presents Δ L r) :
    mPsh Y σ Δ m ψ ↔ ((m.toWeight h.posSet_eq hp).addFn ψ).SemiPos (Y.an σ) := by
  rw [h.mPsh_iff_levi hψ]
  refine ⟨fun H i c y hy ξ => H _ (r i) y hy.1 (ptsIn_subset_eqnSet hp i hy.2) ξ,
    fun H c g y hy hg ξ => ?_⟩
  have hi := mem_pick hp.isLB y
  rw [h.levi_frame hψ hy (ptsIn_subset_eqnSet hp _ hi) hg]
  exact H.chart ((h.isSmooth_toWeight hp).addFn hψ) hy hi ξ

theorem smoothOn_zero : (Y.an σ).SmoothOn univ (0 : Y.pts σ → ℝ) := fun _ => contDiffOn_const

end Var

end GlobalTheory.ProjVar
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Set Filter Topology GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.ChartGlue

namespace GlobalTheory.TrueGeo.InducedSemiPos

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {X Z : Scheme.{0}} {p : X ⟶ Sp k}
  {q : Z ⟶ Sp k'} {j : Z ⟶ X} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts q τ → CxPts p σ}

theorem exists_chart_levi (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (c : AlgChart p σ D) {z : CxPts q τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧
      ∀ (f : CxPts p σ → ℝ) (ξ : Fin D → ℂ), c'.levi (fun w => f (m w)) z ξ = c.levi f (m z) ξ := by
  obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
  have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
    ext a
    rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
  have ho := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  refine ⟨c', hz', fun f ξ => ?_⟩
  rw [AlgChart.levi, AlgChart.levi, he z hz' hz]
  refine congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr
    (eventually_of_mem (ho.mem_nhds (mem_over c'.e hz' hz)) fun v hv => ?_) ξ)
  have e := he _ (c'.e.map_target hv.1) hv.2
  rw [c'.e.right_inv hv.1] at e
  have e' : c.e.symm v = m (c'.e.symm v) := by
    conv_lhs => rw [← e]
    exact c.e.left_inv hv.2
  simp only [e']

theorem semiPos_pull_iff (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (hs : Function.Surjective m) (R : AnRead p σ D) (R' : AnRead q τ D) {B : LB X} {φ : Weight p σ B}
    {φ' : Weight q τ (B.pull j)} (hφ' : φ'.IsSmooth R')
    (e : ∀ i z, φ'.φ i z = φ.φ (i PUnit.unit) (m z)) :
    φ'.SemiPos R' ↔ φ.SemiPosReg D := by
  have hi {a : B.ι} {z : CxPts q τ} (h : m z ∈ ptsIn p σ (B.U a)) : z ∈ ptsIn q τ ((B.pull j).U fun _ => a) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx) ((mem_ptsIn_preimage hm).2 h)
  refine ⟨fun h a c y hy ξ => ?_, fun h => hφ'.semiPos_of_exists fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs y
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm c hy.1
    exact (h.chart hφ' hz' (hi hy.2) ξ).trans_eq
      ((congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ))
  · obtain ⟨a, ha⟩ := R.cover (m z)
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm (R.chart a) ha
    refine ⟨c', _, hz', hi (mem_pick φ.isLB (m z)), fun ξ => ?_⟩
    have h₁ : c'.levi (φ'.φ fun _ => pick φ.isLB (m z)) z ξ = (R.chart a).levi (φ.φ (pick φ.isLB (m z))) (m z) ξ :=
      (congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ)
    exact le_of_le_of_eq (h _ (R.chart a) _ ⟨ha, mem_pick φ.isLB (m z)⟩ ξ) h₁.symm

end BaseChange

section Power

open Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {k : ℕ}

theorem mSmooth_of_mPow (hk : k ≠ 0) (h : mSmooth Y σ _ (mPow Y σ Δ k m)) : mSmooth Y σ Δ m := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  refine ⟨fun y hy => ?_, fun g => ?_⟩
  · have h₁ := mem_eqnSet Δ y
    have h₂ := (Met.mem_posSet_iff (CartierDiv.IsEqn.nsmul h₁ k)).1 (h.1 hy)
    rw [mPow_h h₁] at h₂
    exact lt_of_le_of_ne (m.nonneg _ _) fun e => h₂.ne' (by rw [← e, zero_pow hk])
  · refine AnRead.SmoothOn.congr (f := fun y => (k : ℝ)⁻¹ * (mPow Y σ Δ k m).wt (g ^ k) y)
      (fun c => contDiffOn_const.mul ((h.2 (g ^ k)).mono
        (fun _ hz => ⟨trivial, CartierDiv.IsEqn.nsmul hz.2 k⟩) c)) fun y hy => ?_
    rw [wt_mPow hy.2, inv_mul_cancel_left₀ hk']

theorem mPsh_mPow_iff (hk : k ≠ 0) (h : mSmooth Y σ Δ m) :
    mPsh Y σ _ (mPow Y σ Δ k m) 0 ↔ mPsh Y σ Δ m 0 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have h' : mSmooth Y σ _ (mPow Y σ Δ k m) := Met.SmoothOn.mPow isOpen_univ h k
  have key (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ) (hy : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g) (ξ) :
      c.levi (fun z => (mPow Y σ Δ k m).wt (g ^ k) z + (0 : Y.pts σ → ℝ) z) y ξ =
        k * c.levi (fun z => m.wt g z + (0 : Y.pts σ → ℝ) z) y ξ := by
    simp only [Pi.zero_apply, add_zero]
    rw [AlgChart.levi_congr (isOpen_eqnSet Δ g) hy hg fun z hz => wt_mPow hz k]
    exact AlgChart.levi_const_mul _ (((h.2 g).mono fun _ hz => ⟨trivial, hz⟩).contDiffAt_two
      (isOpen_eqnSet Δ g) hy hg) ξ
  rw [h.mPsh_iff_levi smoothOn_zero, h'.mPsh_iff_levi smoothOn_zero]
  refine ⟨fun H c g y hy hg ξ => ?_, fun H c g y hy hg ξ => ?_⟩
  · have := H c (g ^ k) y hy (CartierDiv.IsEqn.nsmul hg k) ξ
    rw [key c g y hy hg] at this
    exact nonneg_of_mul_nonneg_right this hk'
  · have h₁ := mem_eqnSet Δ y
    rw [h'.levi_frame smoothOn_zero hy (CartierDiv.IsEqn.nsmul h₁ k) hg, key c _ y hy h₁]
    exact mul_nonneg hk'.le (H c _ y hy h₁ ξ)

theorem smooth_psh_of_weight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r) {φ : Weight Y.str σ L}
    (hφ : φ.IsSmooth (Y.an σ)) (t : ℝ)
    (h : ∀ i, ∀ y ∈ ptsIn Y.str σ (L.U i), Real.exp (-t) * m.h (r i) y = Real.exp (-φ.φ i y)) :
    mSmooth Y σ Δ m ∧ (mPsh Y σ Δ m 0 ↔ φ.SemiPos (Y.an σ)) := by
  have h₁ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.h (r i) y = Real.exp (t - φ.φ i y) := by
    rw [sub_eq_add_neg, Real.exp_add, ← h i y hy, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have h₂ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.wt (r i) y = 1 * φ.φ i y + -t := by
    rw [Met.wt, h₁ i y hy, Real.log_exp]
    ring
  have hs : mSmooth Y σ Δ m := Met.smoothOn_of_cover isOpen_univ
    (fun y _ => by
      have hi := mem_pick φ.isLB y
      rw [Met.mem_posSet_iff (ptsIn_subset_eqnSet hp _ hi), h₁ _ y hi]
      exact Real.exp_pos _)
    (fun i => isOpen_ptsIn (L.U i)) (fun y => ⟨_, mem_pick φ.isLB y⟩) (ptsIn_subset_eqnSet hp) fun i =>
    AnRead.SmoothOn.congr (f := fun y => 1 * φ.φ i y + -t)
      (fun c => (contDiffOn_const.mul ((hφ i).mono inter_subset_right c)).add contDiffOn_const)
      fun y hy => h₂ i y hy.2
  refine ⟨hs, ?_⟩
  rw [hs.mPsh_iff_semiPos smoothOn_zero hp]
  refine forall₂_congr fun i c => forall₂_congr fun y hy => forall_congr' fun ξ => ?_
  refine iff_of_eq (congrArg (0 ≤ ·) ((AlgChart.levi_congr (c := (Y.an σ).chart c) (isOpen_ptsIn (L.U i))
    hy.1 hy.2 (g := fun z => 1 * φ.φ i z + -t) (fun z hz => (add_zero _).trans (h₂ i z hz)) ξ).trans ?_))
  refine (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (hφ.contDiffAt_two hy.1 hy.2) 1 (-t) ξ)).trans ?_
  rw [Complex.ofReal_one, one_mul]
  rfl

end Power

theorem mSmooth_and_semiPos_iff : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) ∧ (A.SemiPos ↔ L.SemiPos Y.dim) := by
  intro F _ _ C Y A M L k cf ⟨_, r, hr, hi, _⟩
  obtain rfl := C.eq_std
  have key (σ : F →+* ℂ) : Var.mSmooth Y σ A.D (A.m σ) ∧
      (Var.mPsh Y σ A.D (A.m σ) 0 ↔ (L.φ (σ.comp (algebraMap (𝓞 F) F))).SemiPosReg Y.dim) := by
    obtain ⟨R⟩ := ModelCharts.genSmooth_model F Y M (σ.comp (algebraMap (𝓞 F) F))
    have hm : ∀ z, (bcMap M.pb.w σ z).1 = z.1 ≫ M.j := fun _ => rfl
    let φ : Weight Y.str σ (L.B.pull M.j) :=
      (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => bcMap M.pb.w σ) fun _ => hm
    have hφ : φ.IsSmooth (Y.an σ) := ((Weight.isCInf_iff_isSmooth R).1 (L.cInf _)).linComb _ _ _ _ _
    have e (i z) : φ.φ i z = (L.φ _).φ (i PUnit.unit) (bcMap M.pb.w σ z) :=
      (Fintype.sum_unique fun a : PUnit.{1} =>
        ((1 : ℤ) : ℝ) * (L.φ _).φ (i a) (bcMap M.pb.w σ z)).trans (by simp)
    obtain ⟨h₁, h₂⟩ := smooth_psh_of_weight (m := Var.mPow Y σ A.D k (A.m σ)) hr hφ
      (2 * (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) fun i y hy => by
        have h₃ := Var.ptsIn_subset_eqnSet hr i hy
        have h₄ := hi σ y _ i (((r i)⁻¹ : Y.Fnˣ) : Y.Fn) (hm y) (mem_ptsIn.1 hy) (by
          rw [Units.val_inv_eq_inv_val]
          exact (CartierDiv.isEqn_iff_generatesAt_inv.1 h₃).regularAt)
        rw [Units.inv_mul, Base.ratVal_one, norm_one, one_pow, one_mul] at h₄
        rw [e, ← h₄, ← Var.pn_frame h₃]
    have h₅ := mSmooth_of_mPow k.ne_zero h₁
    exact ⟨h₅, (mPsh_mPow_iff k.ne_zero h₅).symm.trans (h₂.trans
      (semiPos_pull_iff M.pb hm (bijective_bcMap M.pb σ).2 R _ hφ e))⟩
  refine ⟨fun σ => (key σ).1, fun h τ => ?_, fun h σ => ⟨(key σ).1, (key σ).2.2 (h _)⟩⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) (ModelCharts.injective_emb τ),
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) (ModelCharts.injective_emb τ) x⟩
  exact (key σ).2.1 (h σ).2

end GlobalTheory.TrueGeo.InducedSemiPos
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.NefModel

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem charZero_residueField (M : TrueGeo.Model Y) (y : Y.X) : CharZero (M.X.residueField (M.j y)) := by
  let f : F →+* Y.X.residueField y :=
    (Y.X.Γevaluation y).hom.comp (Y.str.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom)
  have : CharZero (Y.X.residueField y) := charZero_of_injective_ringHom f.injective
  exact (M.j.residueFieldMap y).hom.charZero

theorem exists_isClosed (M : TrueGeo.Model Y) {z : M.X} (hz : ArInt.IsAlgPt z) :
    ∃ x : Y.X, IsClosed ({x} : Set Y.X) ∧ M.j x = z := by
  have := hz.1
  let o : Sp F := IsLocalRing.closedPoint F
  have : CharZero ((Sp F).residueField o) := (RingHom.charZero_iff (RingHom.injective
    (Scheme.Spec.residueFieldIso (.of F) o).inv.hom)).1
      ((RingHom.charZero_iff (algebraMap F _).injective).1 inferInstance)
  obtain ⟨x, hx, -⟩ := Scheme.exists_preimage_of_isPullback M.pb z o
    (PrimeSpectrum.ext ((Mean4O.asIdeal_eq_bot M.p z).trans
      (Mean4O.asIdeal_eq_bot (spMap (algebraMap (𝓞 F) F)) o).symm))
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  refine ⟨x, isClosed_of_closure_subset fun y hy => ?_, hx⟩
  have := charZero_residueField M y
  obtain ⟨b, hb, hne⟩ := Mean4O.exists_specializes_ne M.ar (M.j y)
  have hs : z ⤳ M.j y := hx ▸ (specializes_iff_mem_closure.2 hy).map M.j.continuous
  exact M.j.isEmbedding.injective
    (hx.trans (((Mean4O.dim_closure_le_one_iff z).1 hz.2.le _ _ hs hb).resolve_right hne)).symm

theorem card_pos (M : TrueGeo.Model Y) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) :
    0 < Nat.card (M.X.residueField (M.j x) →+* ℂ) := by
  obtain ⟨_, _⟩ := ExtConj.pts Y x hx
  rw [ResidueCard.main F Y M x hx]
  exact mul_pos Module.finrank_pos Nat.card_pos

end GlobalTheory.TrueGeo.NefModel
end
end
