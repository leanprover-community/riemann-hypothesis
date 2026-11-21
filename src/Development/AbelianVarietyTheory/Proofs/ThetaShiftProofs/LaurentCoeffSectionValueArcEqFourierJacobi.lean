import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NfacParallelFlowV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FreqRealNonnegIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType

section
namespace GlobalTheory.LaurentFJ

open Complex ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem coeff_eq_zero_of_hasSum_zero (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by
  have hs : Summable fun k => ‖d k‖ := by
    have := (h 0).summable
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_zpow, mul_one] at this
    exact summable_norm_iff.mpr this
  have hpow : ∀ (k : ℤ) (t : ℝ), cexp (2 * Real.pi * I * t) ^ k * cexp (2 * Real.pi * I * t) ^ (-j)
      = cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t) := by
    intro k t
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1) (f := fun _ : ℝ => (0 : ℂ))
    (F := fun (k : ℤ) (t : ℝ) => d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t))
    (fun k _ => ‖d k‖)
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ fun t _ => by
      have : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t =
          ((2 * Real.pi * ((k - j : ℤ) : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one])
    (MeasureTheory.ae_of_all _ fun t _ => hs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => by
      have := (h t).mul_right (cexp (2 * Real.pi * I * t) ^ (-j))
      simp only [zero_mul, mul_assoc (d _), hpow] at this
      exact this)
  have hval : ∀ k : ℤ, (∫ t in (0 : ℝ)..1,
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)) = if k = j then d j else 0 := by
    intro k
    split_ifs with hk
    · subst hk; simp
    · have hc : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.two_pi_I_ne_zero ?_
        exact_mod_cast sub_ne_zero.mpr hk
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : cexp (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
      simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, this]
      simp
  simp only [hval, intervalIntegral.integral_zero] at hI
  exact (hasSum_ite_eq j (d j)).unique hI

theorem hasSum_fiber_of_hasSum_line {ι : Type*} (c : ι → ℂ) (n : ι → ℤ) (a : ℤ → ℂ) (y : ℝ)
    (f : ℝ → ℂ)
    (ha : ∀ t : ℝ, HasSum (fun k : ℤ => a k * cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t))
    (hc : ∀ t : ℝ, HasSum (fun i => c i * cexp (2 * Real.pi * I * (t + y * I)) ^ n i) (f t))
    (j : ℤ) : HasSum (fun i : {i // n i = j} => c i) (a j) := by
  have hsum : ∀ k : ℤ, Summable fun i : {i // n i = k} => c i := by
    intro k
    have h1 := ((hc 0).summable.subtype fun i => n i = k).mul_right
      (cexp (2 * Real.pi * I * ((0 : ℝ) + y * I)) ^ (-k))
    refine h1.congr fun i => ?_
    have hi : n i = k := i.2
    simp only [Function.comp_apply, hi]
    rw [mul_assoc, ← zpow_add₀ (Complex.exp_ne_zero _)]
    simp
  have hb : ∀ t : ℝ, HasSum (fun k : ℤ => (∑' i : {i // n i = k}, c i) *
      cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t) := by
    intro t
    have h1 := (Equiv.sigmaFiberEquiv n).hasSum_iff.mpr (hc t)
    refine h1.sigma fun k => ?_
    have := (hsum k).hasSum.mul_right (cexp (2 * Real.pi * I * (t + y * I)) ^ k)
    refine this.congr_fun fun i => ?_
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, i.2]
  have hz := coeff_eq_zero_of_hasSum_zero
    (fun k => (a k - ∑' i : {i // n i = k}, c i) * cexp (2 * Real.pi * I * (y * I)) ^ k)
    (fun t => by
      have := (ha t).sub (hb t)
      rw [sub_self] at this
      refine this.congr_fun fun k => ?_
      rw [mul_add, Complex.exp_add, mul_zpow]; ring) j
  have hz' : a j = ∑' i : {i // n i = j}, c i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (zpow_ne_zero _ (Complex.exp_ne_zero _)))
  rw [hz']
  exact (hsum j).hasSum

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem flow_mem_dom_of_im_nonneg (X : Data E r) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV fun τ => Data.emb τ.1 ξ := by
    intro τ
    refine ⟨?_, ?_⟩
    · have key : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        simp only [hermC, herm, Data.emb, map_sum, map_mul, cc,
          NumberField.IsCMField.complexEmbedding_complexConj]
      change hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [key, hξ.2.1, map_zero]
    · intro h0
      apply hξ.2.2
      funext a
      have := congrFun h0 a
      simpa [Data.emb] using this
  refine (flowDomainCriterion_holds r X _ hiv x hx s).1.2 fun τ => ?_
  have ht : 0 < X.ttV (fun τ => Data.emb τ.1 ξ) x τ :=
    one_div_pos.mpr (mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (hiv τ).2))
  have := div_nonneg (hs τ) ht.le
  linarith

theorem hasSum_fj_of_line (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (y : ℝ)
    (hdom : ∀ w : ℂ, w.im = y → X.flow ξ (fun τ => w * sb τ) x ∈ X.dom)
    (ha : ∀ w : ℂ, w.im = y → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  classical
  set n : (X.Ψ → ℝ) → ℤ := fun ν => ⌊2 * ∑ τ, ν τ * sb τ⌋ with hn
  have hnν : ∀ ν, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = n ν := by
    intro ν hν
    obtain ⟨k, hk⟩ := hint ν hν
    simp only [hn, hk, Int.floor_intCast]
  have him : ∀ t : ℝ, ((t : ℂ) + y * I).im = y := fun t => by simp
  have H := hasSum_fiber_of_hasSum_line (fun ν => κ * X.fj la ξ ν P x) n
    (fun k => a k * u₁ ^ k) y (fun t => κ * P (X.flow ξ (fun τ => ((t : ℂ) + y * I) * sb τ) x))
    (fun t => by
      convert ha _ (him t) using 2 with k
      rw [mul_zpow, mul_assoc])
    (fun t => by
      have := (m3bExp_holds r X la P hP ξ hξ x hx _ (hdom _ (him t))).mul_left κ
      refine this.congr_fun fun ν => ?_
      rw [mul_assoc]
      by_cases hν : X.fj la ξ ν P x = 0
      · simp [hν]
      · congr 2
        rw [← Complex.exp_int_mul]
        congr 1
        have h2 : ((n ν : ℤ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * sb τ := by
          have := congrArg (fun z : ℝ => (z : ℂ)) (hnν ν hν)
          push_cast at this
          exact this.symm
        have h3 : ∑ τ, (ν τ : ℂ) * (((t : ℂ) + y * I) * sb τ) =
            ((t : ℂ) + y * I) * ∑ τ, (ν τ : ℂ) * sb τ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        rw [h2, h3]; ring) j
  have e1 := (hasSum_subtype_iff_indicator (s := {ν | n ν = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mp H
  refine (hasSum_subtype_iff_indicator (s := {ν : X.Ψ → ℝ | 2 * ∑ τ, ν τ * sb τ = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mpr ?_
  convert e1 using 1
  funext ν
  by_cases hν : X.fj la ξ ν P x = 0
  · simp [Set.indicator_apply, hν]
  · have : (2 * ∑ τ, ν τ * sb τ = j) ↔ n ν = j := by
      rw [hnν ν hν]; exact Int.cast_inj
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]

theorem hasSum_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  refine hasSum_fj_of_line X hP hξ hx sb hint κ u₁ a (max T 0 + 1) (fun w hw => ?_)
    (fun w hw => ha w (by rw [hw]; linarith [le_max_left T 0])) j
  refine flow_mem_dom_of_im_nonneg X hξ hx _ fun τ => ?_
  simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, hw]
  exact mul_nonneg (by linarith [le_max_right T 0]) (hsb τ)

theorem coeff_mul_zpow_eq_mul_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j * u₁ ^ j = κ * X.fj la ξ ν₀ P x := by
  refine (hasSum_fj X hP hξ hx sb hsb hint κ u₁ a T ha j).unique ?_
  refine hasSum_single (f := fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} =>
    κ * X.fj la ξ ν P x) ⟨ν₀, hj⟩ fun ν hν => ?_
  by_cases h0 : X.fj la ξ ν P x = 0
  · simp [h0]
  · exact absurd (Subtype.ext (huniq ν h0 ν.2)) hν




end

end GlobalTheory.LaurentFJ
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_sectionValue_arc_framedPoint : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  first | exact @GlobalTheory.ArcQ.hasSum_evR_arc | exact GlobalTheory.ArcQ.hasSum_evR_arc | (intros; apply GlobalTheory.ArcQ.hasSum_evR_arc <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix Topology
open MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory

namespace GlobalTheory.AbelianPartNorm

open GlobalTheory.KeyIsoNormal in

theorem exists_unif {P : Out.PolAV (Sp ℂ)} {rig : LB.Gen (P.L.pull (eSec P.A))} {th : P.L.Sec} {v : ℝ}
    (hv : Arch.IsThNormAt P rig th (RingHom.id ℂ) v) :
    ∃ (n : ℕ) (u : HolUnif P.A P.L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin n → ℂ) → ℂ) (Fd : Set (Fin n → ℂ)),
      u.IsAH Hm χ ∧ u.IsRig rig ∧ u.IsFn th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal := by
  obtain ⟨P', rig', th', φ, he, w, hc, hw, hr, hs, u', Hm, χ, θ, Fd, hAH, h₄, h₅, hFd, hv⟩ := hv
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec P.A) _ rig' rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push P.isLB P'.isLB (Over.homMk φ (hc'.1.w.trans (Category.comp_id _))) hc' w
    ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ P.L.U j → (u'.ex z).left pt ∈ P'.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨P'.g, u, Hm, fun l => χ ⟨l.1, hΛ ▸ l.2⟩, θ, Fd, ⟨hAH.1, hAH.2.1, fun l => hAH.2.2.1 _, fun l j z hz => ?_⟩,
    fun j hj => ?_, fun j z hz => ?_, hΛ ▸ hFd, hv⟩
  · rw [hex] at hz
    have hj : φ ((u'.ex z).left pt) ∈ P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart P'.isLB ((u'.ex z).left pt)
    have hl : l.1 ∈ u'.Λ := hΛ ▸ l.2
    have hper : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 hl, _root_.mul_one]
    rw [hfr j k z hj hk, hfr j k (z + l) (hper ▸ hj) (hper ▸ hk), hper,
      hAH.2.2.2 ⟨l.1, hl⟩ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have h0 : (u'.ex 0).left = eSec P'.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[P'.A]).left = η[P'.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart P'.isLB (eSec P'.A pt)
    have hj' : φ (eSec P'.A pt) ∈ P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (P'.L.pull (eSec P'.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart P'.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w th th').1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring

theorem thetaCharOff_eq {g n : ℕ} (S : Finset (Fin g)) (e : Fin n ≃ {k // k ∉ S}) (τ : Matrix (Fin g) (Fin g) ℂ)
    (a b z : Fin g → ℂ) (ha : ∀ k ∈ S, a k = 0) :
    thetaCharOff S τ a b z = thetaChar (τ.submatrix (fun i => (e i).1) (fun i => (e i).1)) (fun i => a (e i).1)
      (fun i => b (e i).1) (fun i => z (e i).1) := by
  classical
  let ε : {m : Fin g → ℤ // ∀ k ∈ S, m k = 0} ≃ (Fin n → ℤ) :=
    { toFun := fun m i => m.1 (e i).1
      invFun := fun m => ⟨fun k => if h : k ∈ S then 0 else m (e.symm ⟨k, h⟩), fun k hk => dif_pos hk⟩
      left_inv := fun m => Subtype.ext (funext fun k => by
        by_cases h : k ∈ S
        · simp [h, m.2 k h]
        · simp [h])
      right_inv := fun m => funext fun i => by simp [(e i).2] }
  have hs : ∀ f : Fin g → ℂ, (∀ k ∈ S, f k = 0) → ∑ k, f k = ∑ i, f (e i).1 := fun f hf => by
    rw [e.sum_comp (fun k => f k.1), ← Finset.sum_subtype Sᶜ (by simp) f, ← Finset.sum_compl_add_sum S,
      Finset.sum_eq_zero hf, add_zero]
  unfold thetaCharOff thetaChar
  rw [← ε.tsum_eq]
  refine tsum_congr fun m => ?_
  have h0 : ∀ k ∈ S, ((fun i => (m.1 i : ℂ)) + a) k = 0 := fun k hk => by simp [m.2 k hk, ha k hk]
  have h1 : ((fun i => ((ε m i : ℤ) : ℂ)) + fun i => a (e i).1) = fun i => ((fun i => (m.1 i : ℂ)) + a) (e i).1 := rfl
  rw [h1]
  generalize ((fun i => (m.1 i : ℂ)) + a) = t at h0
  simp only [dotProduct, Matrix.mulVec]
  rw [hs _ (fun k hk => by rw [h0 k hk, zero_mul]), hs _ (fun k hk => by rw [h0 k hk, zero_mul])]
  simp only [Matrix.submatrix_apply, Pi.add_apply]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs _ (fun k hk => by rw [h0 k hk, mul_zero])]

open GlobalTheory.ThetaMean in
theorem exists_lattice {n : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} (hp : (τ.map Complex.im).PosDef) :
    ∃ Λ : Submodule ℤ (Fin n → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ ∧
      ∀ x, x ∈ Λ ↔ ∃ a b : Fin n → ℤ, x = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := by
  let L : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℂ) := LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hp)
  have hL (p : Fin n ⊕ Fin n → ℝ) : L p = periodMap τ p := rfl
  let b := (Pi.basisFun ℝ (Fin n ⊕ Fin n)).map L
  refine ⟨Submodule.span ℤ (Set.range b), inferInstance, ZSpan.span_top b, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := L.surjective x
  rw [Module.Basis.mem_span_iff_repr_mem]
  have hr (i) : b.repr (L p) i = p i := by simp [b]
  simp only [hr]
  rw [hL]
  constructor
  · intro hz
    choose k hk using hz
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    rw [periodMap_apply]
    simp [← hk]
  · rintro ⟨m, n, hmn⟩
    have : p = Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ)) := by
      apply (periodMap_bijective hp).1
      rw [hmn, periodMap_apply]
      simp
    rintro (i | i)
    · exact ⟨m i, by simp [this]⟩
    · exact ⟨n i, by simp [this]⟩

theorem im_form_real {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (m n m' n' : Fin g → ℝ) :
    (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ⬝ᵥ
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun i => (m' i : ℂ)) + τ *ᵥ (fun i => (n' i : ℂ)))).im =
      n ⬝ᵥ m' - m ⬝ᵥ n' := by
  set Y := τ.map Complex.im with hY
  set X := τ.map Complex.re with hX
  have hXs : X.IsSymm := hs.map _
  have hYs : Y.IsSymm := hs.map _
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have gen : ∀ u v : Fin g → ℂ, (u ⬝ᵥ (Y⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star v).im =
      (fun i => (u i).im) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).re) - (fun i => (u i).re) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).im) := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  have him : ∀ m n : Fin g → ℝ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).im) = Y *ᵥ n := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hY]
  have hre : ∀ m n : Fin g → ℝ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).re) =
      m + X *ᵥ n := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hX]
  have sd : ∀ {M : Matrix (Fin g) (Fin g) ℝ}, M.IsSymm → ∀ u v : Fin g → ℝ, u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
    intro M hM u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  rw [gen, him, him, hre, hre, sd hYs.inv (Y *ᵥ _), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.one_mulVec, add_dotProduct, add_dotProduct,
    dotProduct_comm (X *ᵥ _), dotProduct_comm (X *ᵥ _), sd hXs, dotProduct_comm m' n]
  ring

open GlobalTheory.ThetaMean in

theorem mem_of_integral {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (x : Fin g → ℂ) (hx : ∀ a b : Fin g → ℤ, ∃ k : ℤ, (k : ℝ) = (x ⬝ᵥ
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)))).im) :
    ∃ a b : Fin g → ℤ, x = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := by
  obtain ⟨p, rfl⟩ := (periodMap_bijective hp).2 x
  rw [periodMap_apply] at hx ⊢
  have h : ∀ a b : Fin g → ℤ, ∃ k : ℤ, (k : ℝ) = (fun i => p (.inr i)) ⬝ᵥ (fun i => (a i : ℝ)) -
      (fun i => p (.inl i)) ⬝ᵥ (fun i => (b i : ℝ)) := fun a b => by
    obtain ⟨k, hk⟩ := hx a b
    refine ⟨k, hk.trans ?_⟩
    rw [← im_form_real hs hp]
    simp
  have h1 : ∀ i, ∃ k : ℤ, p (.inl i) = k := fun i => by
    obtain ⟨k, hk⟩ := h 0 (Pi.single i 1)
    refine ⟨-k, ?_⟩
    simp [dotProduct, Pi.single_apply] at hk
    simp [hk]
  have h2 : ∀ i, ∃ k : ℤ, p (.inr i) = k := fun i => by
    obtain ⟨k, hk⟩ := h (Pi.single i 1) 0
    refine ⟨k, ?_⟩
    simp [dotProduct, Pi.single_apply] at hk
    simp [hk]
  choose a ha using h1
  choose b hb using h2
  exact ⟨a, b, by simp [ha, hb]⟩

theorem form_eq {n g : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} {c₁ c₂ : Fin n → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) (h₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2)
    {κ : ℂ} (hκ : κ ≠ 0) {Λ : Submodule ℤ (Fin g → ℂ)} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {χ : Λ → ℂ} (hχ : ∀ l, ‖χ l‖ = 1) {θ : (Fin g → ℂ) → ℂ}
    (hθ : ∀ (l : Λ) z, θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z)
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ a b : Fin n → ℤ, F ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ))) ∈ Λ)
    {ρ : (Fin n → ℂ) → ℂ} (hρ : Differentiable ℂ ρ) (hρn : ∀ x, ρ x ≠ 0) (hρ0 : ρ 0 = 1)
    (e : ∀ x, κ * thetaChar τ c₁ c₂ x = θ (F x) * ρ x) :
    (∀ x y, hermForm Hm (F x) (F y) = x ⬝ᵥ ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star y) ∧
      ∀ x, ‖θ (F x)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (F x) (F x)).re) =
        ‖κ‖ ^ 2 * (‖thetaChar τ c₁ c₂ x‖ ^ 2 * Real.exp (-2 * Real.pi * ((fun i => (x i).im) ⬝ᵥ
          (((τ.map Complex.im)⁻¹) *ᵥ fun i => (x i).im)))) := by
  obtain ⟨Λ₀, d₀, s₀, m₀⟩ := exists_lattice hp
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, H₀ = (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
    (1 : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : (Fin n → ℂ) → ℂ, q = fun z => Real.pi / 2 * (((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ z) ⬝ᵥ
    (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ z))) := ⟨_, rfl⟩
  have hq0 : q 0 = 0 := by simp [hq]
  have hqd : Differentiable ℂ q := by
    rw [hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨an1, an2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy n τ 1 H₀ c₁ c₂ q hs hp h₁ h₂ hH₀ (fun z => by rw [hq])
  simp only [Matrix.one_mulVec] at an1 an2
  obtain ⟨θd, θne⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero n c₁ c₂ h₁ h₂).1 _ hs hp
  have hH₀h : H₀.IsHermitian := hH₀ ▸ (GlobalTheory.ThetaSquareIntegrable.posDef_form hp (by simp)).1
  have hc : ∀ l : Λ₀, ∃ x : ℂ, ‖x‖ = 1 ∧ ∀ z, Complex.exp (q (z + l)) * thetaChar τ c₁ c₂ (z + l) =
      x * Complex.exp (Real.pi * hermForm H₀ z l + Real.pi / 2 * hermForm H₀ l l) *
        (Complex.exp (q z) * thetaChar τ c₁ c₂ z) := fun l => by
    obtain ⟨a, b, h⟩ := (m₀ l).1 l.2
    exact an2 l a b h
  choose χ₀ hχ₀ hl₀ using hc
  have hΛ : ∀ l : Λ₀, F l ∈ Λ := fun l => by
    obtain ⟨a, b, h⟩ := (m₀ l).1 l.2
    rw [h]; exact hF a b
  set H₂ := (LinearMap.toMatrix' F).transpose * Hm * (LinearMap.toMatrix' F).transpose.conjTranspose with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hH
  have hsub : ∀ z w, hermForm (H₀ - H₂) z w = hermForm H₀ z w - hermForm Hm (F z) (F w) := fun z w => by
    have := PullHermitian.hermForm_sub_smul H₀ H₂ 1 1 z w
    rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, PullHermitian.hermForm_pull] at this
  have hrd : Differentiable ℂ fun x => Complex.exp (q x) * ρ x := hqd.cexp.mul hρ
  have key := appellHumbert_trivial_of_nowhere_vanishing n Λ₀ s₀ (H₀ - H₂) (fun l => χ₀ l / χ ⟨F l, hΛ l⟩)
    (fun x => Complex.exp (q x) * ρ x) (hH₀h.sub hH₂h) (fun l => by simp [hχ, hχ₀]) hrd
    (fun x => mul_ne_zero (Complex.exp_ne_zero _) (hρn x)) (fun l z => by
      rw [← sub_eq_zero]
      refine GlobalTheory.ThetaSquareIntegrable.eq_zero_of_entire_mul (D := fun z : Fin n → ℂ => Complex.exp (q (z + l)) * ρ (z + l) -
        χ₀ l / χ ⟨F l, hΛ l⟩ * Complex.exp (Real.pi * hermForm (H₀ - H₂) z l + Real.pi / 2 * hermForm (H₀ - H₂) l l) *
          (Complex.exp (q z) * ρ z)) θd θne ?_ (Filter.Eventually.of_forall fun x => ?_)
      · have c3 := hrd.continuous
        have c4 : Continuous fun z => hermForm (H₀ - H₂) z l := by
          simp only [hermForm, dotProduct]; fun_prop
        exact ((c3.comp (continuous_add_const _)).sub ((continuous_const.mul
          ((continuous_const.mul c4).add continuous_const).cexp).mul c3)).continuousAt
      · have e1 := e x
        have e2 := e (x + l)
        have e3 := hθ ⟨F l, hΛ l⟩ (F x)
        have e4 := hl₀ l x
        rw [map_add, e3] at e2
        have h4 : χ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hχ]; exact one_ne_zero)
        simp only [hsub]
        have e5 : ∀ a b a' b' : ℂ, Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
            Complex.exp (Real.pi * a + Real.pi / 2 * b) / Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
          intro a b a' b'
          rw [← Complex.exp_sub]
          congr 1
          ring
        rw [e5]
        have h7 := Complex.exp_ne_zero (Real.pi * hermForm Hm (F x) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l))
        simp only at e2
        generalize Complex.exp (Real.pi * hermForm Hm (F x) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) = s' at *
        generalize Complex.exp (Real.pi * hermForm H₀ x l + Real.pi / 2 * hermForm H₀ l l) = s at *
        generalize χ ⟨F l, hΛ l⟩ = c at *
        apply mul_left_cancel₀ (mul_ne_zero hκ (mul_ne_zero h4 h7))
        have k1 := mul_inv_cancel₀ h4
        have k2 := mul_inv_cancel₀ h7
        rw [div_eq_mul_inv (χ₀ l), div_eq_mul_inv s]
        linear_combination (c * s' * Complex.exp (q (x + l)) * ρ (x + l)) * e1 -
          (ρ x * Complex.exp (q (x + l))) * e2 + κ * ρ x * e4 -
          κ * thetaChar τ c₁ c₂ x * χ₀ l * s * Complex.exp (q x) * ρ x * (s' * s'⁻¹ * k1 + k2))
  have hf : ∀ x y, hermForm Hm (F x) (F y) = hermForm H₀ x y := fun x y => by
    have h := hsub x y
    rw [key.1] at h
    have h0 : hermForm (0 : Matrix (Fin n) (Fin n) ℂ) x y = 0 := by simp [hermForm]
    rw [h0] at h
    exact (sub_eq_zero.1 h.symm).symm
  refine ⟨fun x y => by rw [hf, hH₀]; simp [hermForm], fun x => ?_⟩
  have h1 := key.2.2 x
  simp only [hq0, hρ0, Complex.exp_zero, _root_.mul_one] at h1
  have h2 : θ (F x) = κ * Complex.exp (q x) * thetaChar τ c₁ c₂ x := by
    linear_combination -(θ (F x)) * h1 - Complex.exp (q x) * e x
  rw [hf, ← an1 x, h2, norm_mul, norm_mul]
  ring

theorem mean_eq {n g : ℕ} {τ : Matrix (Fin n) (Fin n) ℂ} {c₁ c₂ : Fin n → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) (h₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2)
    {κ : ℂ} (hκ : κ ≠ 0) {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hint : ∀ a b : Λ, ∃ k : ℤ, (k : ℝ) = (hermForm Hm a b).im)
    {χ : Λ → ℂ} (hχ : ∀ l, ‖χ l‖ = 1) {θ : (Fin g → ℂ) → ℂ}
    (hθ : ∀ (l : Λ) z, θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z)
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hFs : Function.Surjective F)
    (hF : ∀ a b : Fin n → ℤ, F ((fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ))) ∈ Λ)
    {ρ : (Fin n → ℂ) → ℂ} (hρ : Differentiable ℂ ρ) (hρn : ∀ x, ρ x ≠ 0) (hρ0 : ρ 0 = 1)
    (e : ∀ x, κ * thetaChar τ c₁ c₂ x = θ (F x) * ρ x) {Fd : Set (Fin g → ℂ)}
    (hFd : IsAddFundamentalDomain Λ Fd volume) :
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal =
      ‖κ‖ ^ 2 * (Real.sqrt (2 ^ n * (τ.map Complex.im).det))⁻¹ := by
  obtain ⟨k1, k2⟩ := form_eq hs hp h₁ h₂ hκ hH hχ hθ F hF hρ hρn hρ0 e
  have hFi : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := (GlobalTheory.ThetaSquareIntegrable.posDef_form (h := 1) hp (by simp)).2 x h0
    have h2 := k1 x x
    rw [hx] at h2
    simp [hermForm] at h1 h2
    rw [← h2] at h1
    simp at h1
  let Fe := LinearEquiv.ofBijective F ⟨hFi, hFs⟩
  obtain rfl : n = g := by simpa using Fe.finrank_eq
  obtain ⟨h, hh⟩ : ∃ h, h = LinearMap.toMatrix' Fe.symm.toLinearMap := ⟨_, rfl⟩
  have hm : ∀ x, h *ᵥ F x = x := fun x => by
    rw [hh, LinearMap.toMatrix'_mulVec]
    exact Fe.symm_apply_apply x
  have hu : IsUnit h.det := by
    rw [hh, LinearMap.det_toMatrix']
    exact Fe.symm.isUnit_det'
  have hΛ : ∀ lam, lam ∈ Λ.toAddSubgroup ↔ ∃ a b : Fin n → ℤ,
      h *ᵥ lam = (fun i => (a i : ℂ)) + τ *ᵥ (fun i => (b i : ℂ)) := fun lam => by
    obtain ⟨x, rfl⟩ := hFs lam
    rw [hm]
    constructor
    · intro hx
      refine mem_of_integral hs hp x fun a b => ?_
      rw [← k1]
      exact hint ⟨_, hx⟩ ⟨_, hF a b⟩
    · rintro ⟨a, b, rfl⟩
      exact hF a b
  obtain ⟨Fd', hFd', hI⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar n τ h c₁ c₂ _ hs hp hu h₁ h₂ hΛ
  replace hFd : IsAddFundamentalDomain Λ.toAddSubgroup Fd volume := hFd
  have hcount : Countable Λ.toAddSubgroup := countable_of_Lindelof_of_discrete (X := Λ)
  have hinv : ∀ (l : Λ.toAddSubgroup) (z : Fin n → ℂ), ‖θ (l +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (l +ᵥ z) (l +ᵥ z)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun l z => by
    have : l +ᵥ z = z + (⟨l.1, l.2⟩ : Λ) := add_comm _ _
    rw [this, hθ, AppellHumbertTrivial.re_hermForm_add_self hH, norm_mul, norm_mul, hχ, Complex.norm_exp, _root_.one_mul, mul_pow, ← Real.exp_nat_mul,
      mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    simp
    ring
  have hvol : (volume Fd).toReal = (volume Fd').toReal := by
    simpa [Measure.real] using hFd.setIntegral_eq hFd' (f := fun _ => (1 : ℝ)) fun _ _ => rfl
  rw [hFd.setIntegral_eq hFd' hinv, hvol, ← hI, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
  congr 2
  funext z
  obtain ⟨x, rfl⟩ := hFs z
  rw [k2, hm]

theorem exists_lift_frame (D₀ : Out.DegPre ℂ) {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) {Hm : Matrix (Fin n) (Fin n) ℂ}
    {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) (hrig : u.IsRig D₀.rig) {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ}
    (hθ : u.IsFn th θ) (G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A)) (hadd : ∀ z w, G (z + w) = G z * G w)
    (hhol : IsHolTo Set.univ fun z => (G z).left) (hon : Function.Surjective G) {ψ : (Fin g → ℂ) → ℂ}
    (hψ : IsFnInRigFrame D₀ (fun z => (G z).left) th ψ) :
    ∃ (F : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (ρ : (Fin g → ℂ) → ℂ), Function.Surjective F ∧
      (∀ z, G z = 1 → F z ∈ u.Λ) ∧ (∀ z, (∀ s : ℂ, G (s • z) = 1) → F z = 0) ∧
      Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ ∀ z, ψ z = θ (F z) * ρ z := by
  obtain ⟨-, -, -, -, t1, t2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all D₀.P n u Hm χ hAH
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo D₀.P.A D₀.P.isAb D₀.P.L n g u t1 t2 G hadd hhol
  obtain ⟨fr, f1, f2, f3, f4, f5⟩ := hψ
  have hL := D₀.P.isLB
  have hd := u.discrete
  have hker : ∀ z, G z = 1 → F z ∈ u.Λ := fun z hz => by rw [← u.ker, hF, hz]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : D₀.P.A.left.Opens} {z}, ⊤ ≤ (G z).left ⁻¹ᵁ U → ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := PullHermitian.exists_glue
    (fun i : D₀.P.L.ι => {z | ⊤ ≤ (G z).left ⁻¹ᵁ D₀.P.L.U i})
    (fun i => by simpa using (hhol _ 0).1)
    (fun z => PullHermitian.exists_chart (G z).left hL)
    (fun i z => u.fr i (F z) / fr i z)
    (fun i => by
      have d2 := (u.fr_hol i).comp (s := {z | ⊤ ≤ (G z).left ⁻¹ᵁ D₀.P.L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((f1 i).inv fun z hz => f2 i z hz))
    (fun i j z hi hj => by
      have h1 := f3 i j z (PullHermitian.inf_of _ hi hj)
      have h2 := u.fr_compat i j (F z) (tr (PullHermitian.inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (f2 _ _ hi) (f2 _ _ hj), h1, h2]
      ring)
  refine ⟨F, r, ?_, hker, fun z hz => ?_, hr, fun z => ?_, ?_, fun z => ?_⟩
  · have hc : Countable u.Λ := countable_of_Lindelof_of_discrete
    have hs : Function.Surjective fun l : u.Λ => (LinearMap.range F).mkQ l := fun y => by
      obtain ⟨y, rfl⟩ := (LinearMap.range F).mkQ_surjective y
      obtain ⟨z, hz⟩ := hon (u.ex y)
      have h1 : y - F z ∈ u.Λ := by
        have h2 := u.ex_add (y - F z) (F z)
        rw [sub_add_cancel, hF, hz] at h2
        exact (u.ker _).1 (mul_eq_right.1 h2.symm)
      refine ⟨⟨_, h1⟩, ?_⟩
      simp
    have hq := hs.countable
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    obtain ⟨y, hy⟩ := exists_ne (0 : (Fin n → ℂ) ⧸ LinearMap.range F)
    have hC := (smul_left_injective ℂ hy).countable
    exact not_countable (Complex.ofReal_injective.countable)
  · have hm : ∀ t : ℂ, t • F z ∈ u.Λ := fun t => by
      rw [← map_smul]
      exact hker _ (hz t)
    have hc : Continuous fun t : ℂ => (⟨t • F z, hm t⟩ : u.Λ) :=
      Continuous.subtype_mk (continuous_id.smul continuous_const) _
    have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
    simpa using congrArg Subtype.val h
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u.fr_ne _ _ (tr hi)) (f2 _ _ hi)
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G 0).left hL
    have h0 : (G 0).left = eSec D₀.P.A := by
      rw [← hF, map_zero, (u.ker 0).2 u.Λ.zero_mem]
      change (toUnit _ ≫ η[D₀.P.A]).left = η[D₀.P.A].left
      rw [toUnit_unit, Category.id_comp]
    rw [hrφ i 0 hi, map_zero, div_eq_one_iff_eq (f2 _ _ hi), f4 i hi]
    exact hrig (fun _ => i) fun q hq => mem_pull.2 (by rw [← h0]; exact hi hq)
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (G z).left hL
    have h1 := hθ i (F z) (tr hi)
    rw [hF, f5 i z hi] at h1
    rw [hrφ i z hi, ← mul_div_assoc, ← h1, mul_div_cancel_right₀ _ (f2 _ _ hi)]

theorem fn_automorphy {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {n : ℕ} (u : HolUnif A L n)
    {Hm : Matrix (Fin n) (Fin n) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) {th : L.Sec} {θ : (Fin n → ℂ) → ℂ}
    (hθ : u.IsFn th θ) (l : u.Λ) (z : Fin n → ℂ) :
    θ (z + l) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have h1 := hθ i z hi
  have h2 := hθ i (z + l) (hper ▸ hi)
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  apply mul_right_cancel₀ (u.fr_ne i (z + l) (hper ▸ hi))
  rw [← h2]
  simp only [hermForm]
  ring

theorem norm_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (v : ℝ), Ha.T < w.im → Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → v = ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ := by
  intro _ _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha th Θ w v hw hv
  classical
  obtain ⟨n, u, Hm, χl, θ, Fd, hAH, hrig, hfn, hFd, rfl⟩ := exists_unif hv
  have hj : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  let j : 𝟙_ (Over (Sp ℂ)) ⟶ Out.TF (R := ℂ) ℂ := Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans hj)
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ a.D₀.P.A) := fun z =>
    Over.homMk (Ha.ex₀ z).b.left ((Over.w _).trans hj)
  have hG : ∀ z, G z = j ≫ (Ha.ex₀ z).b := fun z => Over.OverMorphism.ext (Category.id_comp _).symm
  have hG1 : ∀ z, (Ha.ex₀ z).b = Out.DegPre.zeroF a.D₀ ℂ → G z = 1 := fun z hz => by
    rw [hG, hz]
    exact MonObj.comp_one j
  obtain ⟨F, ρ, Fs, Fk, F0, ρd, ρn, ρ0, hρ⟩ := exists_lift_frame a.D₀ u hAH hrig hfn G
    (fun z z' => by
      rw [hG, hG, hG, (Ha.add z z').1]
      exact MonObj.comp_mul j _ _) Ha.hol_b
    (fun p => by
      obtain ⟨x, hx⟩ := GlobalTheory.TorusExt.exists_lift (D := a.D₀) (F := ℂ) (toUnit _ ≫ p)
      obtain ⟨z, rfl⟩ := Ha.onto x
      refine ⟨z, ?_⟩
      rw [hG, hx, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (𝟙 _), Category.id_comp]) (Θ.onB w hw)
  obtain ⟨hs, hp⟩ := Θ.pos w hw
  have hm := GlobalTheory.ThetaSquareIntegrable.mulVec_period (Ha.Pw w) Θ.bas Θ.h (Θ.τ w) (Θ.per w)
  have hh : IsUnit Θ.h.det := by
    have : Θ.h * (Matrix.of fun i k => Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)) i) = 1 := by
      ext i k
      have := congrFun (Θ.per w k).1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply] using this
    exact Matrix.isUnit_det_of_right_inverse this
  have hi1 : ∀ z, Θ.h⁻¹ *ᵥ (Θ.h *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hh, Matrix.one_mulVec]
  have hi2 : ∀ z, Θ.h *ᵥ (Θ.h⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  have hP : ∀ t, F (Ha.Pw w t) = F (Ha.P₀ t) := fun t => by
    rw [Ha.Pw_eq, map_add, map_smul, F0 _ fun s => hG1 _ (Ha.shift s t).1, smul_zero, add_zero]
  have hS : ∀ k ∈ Θ.S, F (Θ.h⁻¹ *ᵥ Pi.single k 1) = 0 := fun k hk => by
    rw [← (Θ.per w k).1, hi1, hP]
    have h1 := (Ha.riemann _).1 ((Θ.orth (Pi.single (.inl k) 1)).2 ⟨fun k' => by simp, fun k' hk' => by
      have : k' ≠ k := fun e => hk' (e ▸ hk)
      simp [this]⟩)
    exact F0 _ fun s => hG1 _ (h1.2 s).choose_spec.1.1
  let e : Fin (g - Θ.S.card) ≃ {k // k ∉ Θ.S} := (Fintype.equivFinOfCardEq (by simp)).symm
  let ext : (Fin (g - Θ.S.card) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := fun x k => if h : k ∈ Θ.S then 0 else x (e.symm ⟨k, h⟩)
      map_add' := fun x y => funext fun k => by by_cases h : k ∈ Θ.S <;> simp [h]
      map_smul' := fun s x => funext fun k => by by_cases h : k ∈ Θ.S <;> simp [h] }
  have hext : ∀ x i, ext x (e i).1 = x i := fun x i => by simp [ext, (e i).2]
  let L := Θ.h⁻¹.mulVecLin ∘ₗ ext
  let F' := F ∘ₗ L
  have hF' : ∀ y, F' (fun i => y (e i).1) = F (Θ.h⁻¹ *ᵥ y) := fun y => by
    have h1 : y = ext (fun i => y (e i).1) + ∑ k ∈ Θ.S, y k • Pi.single k 1 := by
      funext k
      by_cases h : k ∈ Θ.S <;> simp [ext, h, Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [h1]
    rw [Matrix.mulVec_add, map_add, Matrix.mulVec_sum, map_sum, Finset.sum_eq_zero fun k hk => by
      rw [Matrix.mulVec_smul, map_smul, hS k hk, smul_zero], add_zero]
    rfl
  have hinj : Function.Injective fun i => (e i).1 := Subtype.val_injective.comp e.injective
  obtain ⟨Ef, hEf, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all a.D₀.P n u Hm χl hAH
  have hd := u.discrete
  have key := mean_eq (τ := (Θ.τ w).submatrix (fun i => (e i).1) (fun i => (e i).1)) (c₁ := fun i => Θ.c₁ (e i).1)
    (c₂ := fun i => Θ.c₂ (e i).1) (hs.submatrix _) (hp.submatrix hinj) (fun i => Θ.half₁ _) (fun i => Θ.half₂ _)
    Θ.κ_ne hAH.1 (fun x y => ⟨Ef x y, hEf x y⟩) hAH.2.2.1 (fn_automorphy a.D₀.P.isLB u hAH hfn) F'
    (fun y => by
      obtain ⟨z, rfl⟩ := Fs y
      exact ⟨_, (hF' (Θ.h *ᵥ z)).trans (by rw [hi1])⟩)
    (fun p q => by
      let t : Fin g ⊕ Fin g → ℤ := Sum.elim (fun k => if h : k ∈ Θ.S then 0 else p (e.symm ⟨k, h⟩))
        (fun k => if h : k ∈ Θ.S then 0 else q (e.symm ⟨k, h⟩))
      have h1 : Ha.y (Θ.bas t) = 0 := (Θ.ker t).2 fun k hk => by simp [t, hk]
      have h2 := Fk _ (hG1 _ ((Ha.ker _).2 ⟨_, h1, rfl⟩).1)
      rw [← hP, ← hi1 (Ha.Pw w _), ← hF', hm] at h2
      convert h2 using 2
      funext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      congr 1
      · simp [t, (e i).2]
      · rw [← Finset.sum_compl_add_sum Θ.S, Finset.sum_eq_zero (s := Θ.S) fun k hk => by simp [t, hk], add_zero,
          Finset.sum_subtype (p := fun k => k ∉ Θ.S) Θ.Sᶜ (by simp), ← e.sum_comp]
        exact Finset.sum_congr rfl fun k _ => by simp [t, (e k).2])
    (ρ := fun x => ρ (L x)) (ρd.comp L.toContinuousLinearMap.differentiable) (fun x => ρn _)
    (by simp only [map_zero, ρ0])
    (fun x => by
      have h1 := hρ (L x)
      have h2 : Θ.h *ᵥ L x = ext x := hi2 _
      simp only [h2] at h1
      rw [thetaCharOff_eq Θ.S e _ _ _ _ Θ.c₁_S] at h1
      simp only [hext] at h1
      exact h1) hFd
  refine key.trans ?_
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

end GlobalTheory.AbelianPartNorm
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (v : ℝ), Ha.T < w.im → Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → v = ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ := by
  atlas_forward_decl GlobalTheory.AbelianPartNorm.norm_eq
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_l2_family_uniform_compare : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Pm' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (s : CAt σ) (v v' : ℝ), IsPeriod (Fu.Di i) ty Pm → IsPeriod (Fu.Di i') ty Pm' → y.x = Fu.u i Pm → y'.x = Fu.u i' Pm' → FrChg G s y y' → IsThetaL2NormSquared Fu i Pm y v → IsThetaL2NormSquared Fu i' Pm' y' v' → 0 < v ∧ v' = ‖toC s‖ ^ 2 * v := by
  first | exact @GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | exact GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | (intros; apply GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ValNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_idx (hσ : GoodEmb c σ) (X : Data E r) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j,
      (X.p0 ≤ ((idx j).2 : ℕ) ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (((idx j).2 : ℕ) < X.p0 ∧ conjEmb (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0)) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < X.p0 then
          hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · exact Or.inl ⟨by omega, b, c'⟩
    · exact Or.inr ⟨by omega, by rw [b]; exact hcc _, c', d⟩
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl

theorem exists_move (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (x b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) :
    ∃ h₀ : Matrix (Fin g) (Fin g) ℂ,
      (∀ v : Fin r → E, (fun j => perFr (U.X k) (rmul x b) v (relab c σ (e j).1) (e j).2) =
        h₀ *ᵥ fun j => perFr (U.X k) x v (relab c σ (e j).1) (e j).2) ∧
      (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∏ j, h₀⁻¹ j j ^ (a ((e j).1, (e j).2) + n / 2) = bchar (laU U a n k) b := by
  obtain ⟨idx, hi, hper⟩ := exists_idx hσ (U.X k) hr hp0 hty e
  obtain ⟨hbij, -, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega)] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
      · omega
    · rw [if_pos a1] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · omega
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (U.X k).p0 idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (U.X k).p0 idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (U.X k).p0 idx b, fun v => ?_, PerBor.inv_support _ _ _ hu hs, fun a n => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (U.X k).Gm x v _ _ (fun j => hper _ _ j) (fun j => hper _ _ j)
  · unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (U.X k).Ψ) (i : Fin r) => b τ i i ^ laU U a n k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, hdiag]
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega), if_pos a1, b1, hinv,
        show ((idx j).2 : ℕ) - (U.X k).p0 = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
    · rw [if_pos a1, if_neg (by omega), b1, hinv,
        show (U.X k).p0 - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring

theorem exists_frBor (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0)
    (x : (U.X k).dom) (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (h : rmul x.1 b ∈ (U.X k).dom) :
    ∃ (t : Ix Dw → (CAt σ)ˣ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)),
      FrBor t (U.un k x) (U.un k ⟨_, h⟩) ∧ FrChg G (t none : CAt σ) (U.un k x) (U.un k ⟨_, h⟩) ∧
      ∀ a n, toC (wchar (ex Dw a n) t) * bchar (laU U 0 n k) b =
        toC (t none : CAt σ) ^ n * bchar (laU U a n k) b := by
  obtain ⟨h₀, hP, htri, hw⟩ := exists_move hσ U k hr hp0 hty Uw.e x.1 b hb
  have hp := Uw.period k x
  have hp' := Uw.period k ⟨_, h⟩
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F (Uw.ik k)
    (Uw.Pm k x) (Uw.Pm k ⟨_, h⟩) (LinearEquiv.refl _ _) h₀ hp hp' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) (fun a => by
      have e1 : Uw.Pm k x a = _ := funext (Uw.Pm_eq k x a)
      have e2 : Uw.Pm k ⟨_, h⟩ a = _ := funext (Uw.Pm_eq k ⟨_, h⟩ a)
      rw [LinearEquiv.refl_apply, e1, e2]
      exact hP _)
  obtain ⟨hy1, hy2⟩ := Uw.lie k x
  obtain ⟨hy1', hy2'⟩ := Uw.lie k ⟨_, h⟩
  have hxx : (U.un k ⟨_, h⟩).x = (U.un k x).x := hy1'.trans (hu.symm.trans hy1.symm)
  have hder : ∀ τ i, IsDerivAt0 (fun z => (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left)
      (h₀⁻¹ *ᵥ Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ((U.un k ⟨_, h⟩).u τ i) := by
    intro τ i
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) hp (Uw.ik k)
      (Uw.Pm k ⟨_, h⟩) (Matrix.mulVecLin h₀) hp' hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy2' τ i
  obtain ⟨G, t₀, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).1 hxx
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := GlobalTheory.NormUnBor.diag_ne_zero Uw.e h₀⁻¹ hinv htri
  let d : Fin Uw.g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (Uw.e.symm p))
  refine ⟨t, G, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (Uw.e.symm ⟨τ, i'⟩) (Uw.e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩,
    hG, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [Uw.e.apply_symm_apply, Uw.e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F _ _ hp _ _ _ (hy2 τ) _ _).2 ?_
    rw [GlobalTheory.NormUnBor.col_eq_sum Uw.e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hG.2.2
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n
    rw [← hw a n, ← hw 0 n]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) * _ = _
    rw [Fintype.prod_option, mul_assoc]
    congr 1
    rw [← Equiv.prod_comp Uw.e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (Uw.e.symm (Uw.e j)) (Uw.e.symm (Uw.e j)) ^ a ((Uw.e j).1, (Uw.e j).2) * _ = _
    rw [Uw.e.symm_apply_apply, ← pow_add, Pi.zero_apply, zero_add]

theorem exists_unit (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ ∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1 := by
  obtain ⟨_, b, hb, hg, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun τ i => ?_⟩
  unfold dmin lminor
  rw [hg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

end GlobalTheory.ValNorm
end

section
open Complex

namespace GlobalTheory

theorem exists_const_ratio_of_norm_eq :
    ∀ (I : Type) (T K : ℝ) (f g : I → ℂ → ℂ) (c : ℂ → ℂ), 0 < K →
      (∀ i, DifferentiableOn ℂ (f i) {w | T < w.im} ∧ DifferentiableOn ℂ (g i) {w | T < w.im}) →
      (∀ i w, T < w.im → f i w = c w * g i w ∧ ‖f i w‖ = K * ‖g i w‖) →
      ∃ κ : ℂ, ‖κ‖ = K ∧ ∀ i w, T < w.im → f i w = κ * g i w := by
  intro I T K f g c hK hd h
  by_cases h0 : ∀ i w, T < w.im → g i w = 0
  · refine ⟨K, by simp [abs_of_pos hK], fun i w hw => ?_⟩
    rw [(h i w hw).1, h0 i w hw]; simp
  push_neg at h0
  obtain ⟨i₀, w₀, hw₀, hg₀⟩ := h0
  have hU : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | T < w.im} := (convex_halfSpace_im_gt T).isPreconnected
  have hca : ContinuousAt (g i₀) w₀ :=
    (hd i₀).2.continuousOn.continuousAt (hU.mem_nhds hw₀)
  have hev : ∀ᶠ w in nhds w₀, T < w.im ∧ g i₀ w ≠ 0 :=
    (hU.eventually_mem hw₀).and (hca.eventually_ne hg₀)
  obtain ⟨r, hr, hB⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball w₀ r ⊆ {w : ℂ | T < w.im} := fun w hw => (hB w hw).1
  have hcq : ∀ w ∈ Metric.ball w₀ r, c w = f i₀ w / g i₀ w := fun w hw => by
    rw [(h i₀ w (hB w hw).1).1, mul_div_cancel_right₀ _ (hB w hw).2]
  have hcd : DifferentiableOn ℂ c (Metric.ball w₀ r) :=
    (((hd i₀).1.mono hsub).div ((hd i₀).2.mono hsub) fun w hw => (hB w hw).2).congr hcq
  have hcn : ∀ w ∈ Metric.ball w₀ r, ‖c w‖ = K := fun w hw => by
    rw [hcq w hw, norm_div, (h i₀ w (hB w hw).1).2,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hB w hw).2)]
  have hm : w₀ ∈ Metric.ball w₀ r := Metric.mem_ball_self hr
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball w₀ r).isPreconnected Metric.isOpen_ball hcd hm
    (fun w hw => by
      show ‖c w‖ ≤ ‖c w₀‖
      rw [hcn w hw, hcn w₀ hm])
  refine ⟨c w₀, hcn w₀ hm, fun i w hw => ?_⟩
  have ha : AnalyticOnNhd ℂ (f i) {w : ℂ | T < w.im} := (hd i).1.analyticOnNhd hU
  have hb : AnalyticOnNhd ℂ (fun w => c w₀ * g i w) {w : ℂ | T < w.im} :=
    ((hd i).2.const_mul (c w₀)).analyticOnNhd hU
  have he : f i =ᶠ[nhds w₀] fun w => c w₀ * g i w := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr] with z hz
    rw [(h i z (hB z hz).1).1, hconst hz]
    rfl
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hUc hw₀ he hw

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_letter_analyticVectors_independent_blockType : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Mono Y.j → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) := by
  first | exact @GlobalTheory.ArcType.main | exact GlobalTheory.ArcType.main | (intros; apply GlobalTheory.ArcType.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcCoeff

theorem norm_eTwoPi_zpow (w : ℂ) (m : ℤ) : ‖eTwoPi w ^ m‖ = Real.exp (-(2 * Real.pi * m) * w.im) := by
  unfold eTwoPi
  rw [← Complex.exp_int_mul, Complex.norm_exp]
  congr 1
  simp
  ring

theorem differentiableOn_of_hasSum (a : ℤ → ℂ) (T : ℝ) (f : ℂ → ℂ)
    (h : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m) (f w)) :
    DifferentiableOn ℂ f {w | T < w.im} := by
  intro w₀ hw₀
  have hw₀' : T < w₀.im := hw₀
  set y₁ : ℝ := (T + w₀.im) / 2 with hy₁
  set y₂ : ℝ := w₀.im + 1 with hy₂
  have hs : ∀ y : ℝ, T < y → Summable fun m : ℤ => ‖a m‖ * Real.exp (-(2 * Real.pi * m) * y) := fun y hy => by
    have := (h (y * Complex.I) (by simpa using hy)).summable.norm
    simpa only [norm_mul, norm_eTwoPi_zpow, Complex.mul_I_im, Complex.ofReal_re] using this
  have hO : IsOpen {w : ℂ | y₁ < w.im ∧ w.im < y₂} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hd : DifferentiableOn ℂ (fun w => ∑' m : ℤ, a m * eTwoPi w ^ m) {w : ℂ | y₁ < w.im ∧ w.im < y₂} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((hs y₁ (by linarith)).add (hs y₂ (by linarith))) (fun m => ?_) hO (fun m w hw => ?_)
    · have : (fun w => a m * eTwoPi w ^ m) = fun w => a m * Complex.exp (m * (2 * Real.pi * Complex.I * w)) := by
        funext w
        rw [Complex.exp_int_mul]
        rfl
      rw [this]
      fun_prop
    · rw [norm_mul, norm_eTwoPi_zpow, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rcases le_total 0 (2 * Real.pi * m) with hm | hm
      · exact le_add_of_le_of_nonneg (Real.exp_le_exp.2 (by nlinarith [hw.1])) (Real.exp_pos _).le
      · exact le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 (by nlinarith [hw.2]))
  have hm : {w : ℂ | y₁ < w.im ∧ w.im < y₂} ∈ nhds w₀ := hO.mem_nhds ⟨by linarith, by linarith⟩
  refine ((hd.differentiableAt hm).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hm] with w hw
  exact (h w (by linarith [hw.1])).tsum_eq.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem two_sum_eq_trace (X : Data E r) {ν s : E} (hν : cc ν = ν) (hs : cc s = s) :
    2 * ∑ τ : X.Ψ, (τ.1 ν).re * (τ.1 s).re = ((Algebra.trace ℚ E (ν * s) : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, X.trace_eq_Psi]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, RealEmbeddingCharacters.emb_real hs, RealEmbeddingCharacters.emb_real hν, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.ofReal_re, Complex.ofReal_re]
  ring

theorem coeff_eq_of_betaAt (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P)
    {ξ' : Fin r → E} (hξ : X.IsIso ξ') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ξ : Module.Dual ℤ M) (N : ℕ) (be : LinearMap.BilinForm ℤ M)
    (hbe : ∀ y z, (N : ℤ) ∣ be y z) {ν₀ sE : E} {jj : ℤ} (hβ : BetaAt ξ N be ν₀ jj) (hs : IsBePar ξ be sE)
    (hpos : ∀ τ : X.Ψ, 0 < (τ.1 sE).re) (hT : TransvIn X N la)
    (hlev : ∀ s : E, LevelPar ξ N s → ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm ξ' (s * X.κ0)).mulVec v - v = (N : E) • u)
    (κ w₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m)
      (κ * P (X.flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x))) :
    a jj * eTwoPi w₁ ^ jj = κ * X.fj la ξ' (fun τ => (τ.1 ν₀).re) P x := by
  obtain ⟨hν₀, hβ⟩ := hβ
  obtain ⟨htr, huq⟩ := hβ sE hs
  have hsL : LevelPar ξ N sE := ⟨hs.1, fun y z => by
    obtain ⟨m, hm⟩ := hbe y z
    exact ⟨m, by rw [hs.2, hm]; push_cast; rfl⟩⟩
  have hfr : ∀ ν : X.Ψ → ℝ, X.fj la ξ' ν P x ≠ 0 → ∃ ν₁ : E, cc ν₁ = ν₁ ∧ (ν = fun τ => (τ.1 ν₁).re) ∧
      (∀ τ : E →+* ℂ, 0 ≤ (τ ν₁).re) ∧ ∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν₁ * s) = m := by
    intro ν hν
    obtain ⟨ν₁, h1, h2, h3, h4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r X la P hP ξ' hξ ν x hx hν
    exact ⟨ν₁, h1, funext h2, h3, fun s hs' => h4 s hs'.1 (hT ξ' hξ s hs'.1 (hlev s hs'))⟩
  refine GlobalTheory.LaurentFJ.coeff_mul_zpow_eq_mul_fj X hP.1 hξ hx (fun τ => (τ.1 sE).re) (fun τ => (hpos τ).le) _ jj
    ?_ (fun ν hν hj => ?_) (fun ν hν => ?_) κ _ a (T - w₁.im) (fun w hw => ?_)
  · rw [two_sum_eq_trace X hν₀ hs.1, htr, Rat.cast_intCast]
  · obtain ⟨ν₁, h1, rfl, h3, h4⟩ := hfr ν hν
    rw [two_sum_eq_trace X h1 hs.1] at hj
    rw [huq ν₁ h1 h3 h4 (by exact_mod_cast hj)]
  · obtain ⟨ν₁, h1, rfl, -, h4⟩ := hfr ν hν
    obtain ⟨m, hm⟩ := h4 sE hsL
    exact ⟨m, by rw [two_sum_eq_trace X h1 hs.1, hm, Rat.cast_intCast]⟩
  · have := ha (w₁ + w) (by rw [Complex.add_im]; linarith)
    simp only [add_sub_cancel_left, eTwoPi, mul_add, Complex.exp_add] at this
    exact this

theorem frChg_of_anLie {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) (y y' : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (h : AnLie Fu i Pm y z) (h' : AnLie Fu i Pm y' z) :
    ∃ s, FrChg (fun _ => 1) s y y' := by
  have hx : y'.x = y.x := h'.1.trans h.1.symm
  obtain ⟨G, s, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Fu i _ hP
  refine ⟨s, hx, fun τ k => ?_, hG.2.2⟩
  rw [(hder _).unique (h'.2 τ k) (h.2 τ k)]
  exact (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) y y y).1.2.1 τ k

theorem evR_eq_and_norm (hL : Out.Laws) (hL2 : Out.Laws2) (U : Unf Xo c σ r) (Uw : UnfWit U)
    (hEv : GlobalTheory.Reg.EvLaws Xo c) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom)
    (y : FrPt Xo c (CAt σ)) (s : CAt σ) (v : ℝ) (hchg : FrChg (fun _ => 1) s (U.un k x) y)
    (i : Fin Uw.F.n) (Pm : (Uw.F.Di i).La →+ (Fin Uw.g → ℂ)) (hPm : IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) Pm)
    (hy : y.x = Uw.F.u i Pm) (hv : IsThetaL2NormSquared Uw.F i Pm y v) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c)
    (hD : Dom a n) (hF : F ∈ sec Xo c a n) :
    toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 ∧
      ‖toC (evR Xo c F y)‖ = v ^ ((n : ℝ) / 2) * ‖rdU U F k x.1‖ * (U.X k).nfac (laU U 0 n k) x.1 := by
  obtain ⟨hr, hty, -, -, hsec, -⟩ := hU
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨b, hb, h, hun⟩ := GlobalTheory.ValNorm.exists_unit (U.X k) x.2
  obtain ⟨t, G, hbor, hG, hw⟩ := GlobalTheory.ValNorm.exists_frBor hσ U Uw k hr (hty k).1 (hty k).2 x b hb h
  obtain ⟨G', a₀, -, hG'⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y (U.un k ⟨_, h⟩)).1
    (hG.1.trans hchg.1.symm)
  have hts : (t none : CAt σ) = a₀ * s :=
    ((GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).2 _ _ _ _ hG
      ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) _ _ _).2 _ _ _ _ hchg hG')).2
  obtain ⟨hv0, hv1⟩ := GlobalTheory.T.theta_l2_family_uniform_compare hL hL2 E H Dw l Xo c σ _ _ Uw.F _ _ _ _ y _ G' _ v 1 hPm
    (Uw.period k ⟨_, h⟩) hy (Uw.lie k ⟨_, h⟩).1 hG' hv (Uw.norm k ⟨_, h⟩ hun)
  obtain ⟨hB, hS⟩ := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hEv a n F hF (CAt σ)).2 inferInstance
  have hrd : ∀ z : (U.X k).dom, rdU U F k z.1 = toC (evR Xo c F (U.un k z)) := fun z => dif_pos z.2
  have e1 : toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 := by
    rw [hrd]; exact hS s _ _ hchg
  have e2 : toC (wchar (ex Dw a n) t) * rdU U F k x.1 = bchar (laU U a n k) b * rdU U F k x.1 := by
    rw [← (hsec a n hD F hF k).2.1 x.1 x.2 b hb, hrd x]
    exact ((hrd ⟨_, h⟩).trans (hB t _ _ hbor)).symm
  have e3 : (U.X k).nfac (laU U 0 n k) x.1 = ‖bchar (laU U 0 n k) b‖ := by
    rw [← GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul (U.X k) _ x.2 hb]
    unfold Data.nfac
    simp only [norm_div, hun, div_one, Real.one_rpow, Finset.prod_const_one, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1, e3]
  by_cases hP : rdU U F k x.1 = 0
  · simp [hP]
  have e4 := hw a n
  rw [mul_right_cancel₀ hP e2, mul_comm] at e4
  have e5 := mul_right_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne (U.X k) _ hb) e4
  have e6 : toC (t none : CAt σ) = toC (a₀ : CAt σ) * toC s := hts
  have e7 : v ^ ((n : ℝ) / 2) * ‖toC (a₀ : CAt σ)‖ ^ n = 1 := by
    obtain ⟨m, rfl⟩ := hD.2
    rw [show (((m + m : ℕ) : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, ← two_mul, pow_mul,
      ← mul_pow, mul_comm, ← hv1, one_pow]
  rw [e5, e6, norm_mul, norm_pow, norm_pow, norm_mul, mul_pow]
  linear_combination (-(‖toC s‖ ^ n * ‖rdU U F k x.1‖)) * e7

theorem tau_col_const [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty}
    (Ha : HolArc Y σ a χ W Fu) {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th) (w w' : ℂ) (j k : Fin g) (hk : k ∉ Θ.S) :
    Θ.τ w j k = Θ.τ w' j k := by
  obtain ⟨nn, h1, -, -, h4, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hy : Ha.y (Θ.bas (Pi.single (.inr k) 1)) = 0 := (Θ.ker _).2 fun k' hk' =>
    Pi.single_eq_of_ne (fun h => hk (by rwa [← Sum.inr_injective h])) _
  have hN : Ha.N (Θ.bas (Pi.single (.inr k) 1)) = 0 := by rw [h1, h4 _ hy, map_zero]
  have e := (Θ.per w k).2
  rw [Ha.Pw_eq, hN, smul_zero, ← smul_zero w', ← hN, ← Ha.Pw_eq, (Θ.per w' k).2] at e
  simpa using (congrFun e j).symm

theorem coeff_evR_eq_fj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ th ξ ν₀ jj a' n hEv hσ hU halg hχ hmono hpush hth
    hrk hξ0 hβ hD hTr w₁ hw₁
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e) th hth
  obtain ⟨k, ξ', sE, hiso, hbe, hpos, hlev, hdict⟩ :=
    GlobalTheory.ArcFlow.holArc_eq_flow_orbit hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha hσ hU hrk ξ hξ0 w₁ hw₁
  obtain ⟨C₀, hC₀, hC₀', hcov⟩ := GlobalTheory.LatticeCovolumeL2.det_im_eq_covol E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hσ hU hiso hrk
  set B : ℝ := ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w₁).map Complex.im).submatrix
    (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ with hBdef
  have hB : 0 < B := by
    have h1 := ((Θ.pos w₁ hw₁).2.submatrix (e := fun k : {k // k ∉ Θ.S} => k.1) Subtype.val_injective).det_pos
    have h2 := norm_pos_iff.2 Θ.κ_ne
    positivity
  refine ⟨k, ξ', sE, B * C₀, hiso, hbe, hpos, hlev, mul_pos hB hC₀, fun v hv => ?_, fun e z y hy hz => ?_⟩
  · rw [GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w₁ v hw₁ hv]
    exact mul_le_mul_of_nonneg_left hC₀' hB.le
  have hzt := GlobalTheory.T.arc_letter_analyticVectors_independent_blockType hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha y e th z hσ halg (GlobalTheory.ThetaShiftProofs.mono_j Y hmono) hy hz
  obtain ⟨x, hx, L, γ, hEF, hLz, ⟨t, ht, htξ⟩, hflow⟩ := hdict z hzt
  obtain ⟨T', hT'⟩ := GlobalTheory.T.hasSum_sectionValue_arc_framedPoint hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha y e th Θ z hEv halg hχ hmono hpush hth hy hz
  set K : ℝ := (B * C₀ * ∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x with hKdef
  have htt : ∀ x' ∈ (U.X k).dom, 0 < ∏ τ, ((U.X k).tt ξ' x' τ)⁻¹ := fun x' hx' =>
    Finset.prod_pos fun τ _ => inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso hx' τ)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos (mul_pos hB hC₀) (htt x hx)) _)
    (MinimumGrowthBounds.nfac_pos _ _ hx)
  let fl : ℂ → Frame (U.X k).Ψ r := fun w => (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x
  have key : ∀ w : ℂ, ∃ cw : ℂ, max Ha.T T' < w.im → ∀ F ∈ sec Xo c a' n,
      HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (cw * rdU U F k (fl w)) ∧
        ‖cw * rdU U F k (fl w)‖ = K * ‖rdU U F k (fl w)‖ := by
    intro w
    by_cases hw : max Ha.T T' < w.im
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
    obtain ⟨hxw, hPm, hlie⟩ := hflow w hw1
    obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ z hσ hzt w hw1
    obtain ⟨s, hs⟩ := frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw1) _ _ z hlie hyw.1
    have hv := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w yw hw1 hyw.1.1 hyw.2
    have hoff : (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) =
        (((Θ.τ w₁).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) := by
      ext i j
      exact congrArg Complex.im (tau_col_const Ha Θ w w₁ i.1 j.1 j.2)
    rw [hcov w ⟨_, hxw⟩ L γ hw1 hPm hEF ⟨t, fun v' hv' => by
      have := ht v'
      rwa [hv', map_zero, neg_eq_zero] at this, htξ⟩, hoff, ← mul_assoc, ← mul_assoc, ← hBdef] at hv
    refine ⟨toC s ^ n, fun _ F hF => ?_⟩
    obtain ⟨e1, e2⟩ := evR_eq_and_norm hL hL2 U Uw hEv hσ hU k ⟨_, hxw⟩ yw s _ hs Ha.i _ (Ha.period w hw1) hyw.1.1 hv
      a' n F hD hF
    have hsum := hT' w hw2 yw hyw a' n F hF
    rw [e1] at hsum e2
    refine ⟨hsum, e2.trans ?_⟩
    have hn := GlobalTheory.ArcQ.nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hD.2 hiso x hx _ hxw
    rw [hKdef, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hxw).le, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hx).le]
    dsimp only [fl]
    linear_combination ((B * C₀) ^ ((n : ℝ) / 2) * ‖rdU U F k (fl w)‖) * hn
  choose cw hcw using key
  have hfl : Differentiable ℂ fl := (FlowMeanContinuity.flow_differentiable (U.X k) ξ' x).comp (by fun_prop)
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.exists_const_ratio_of_norm_eq {F // F ∈ sec Xo c a' n} (max Ha.T T') K
    (fun F w => cw w * rdU U F.1 k (fl w)) (fun F w => rdU U F.1 k (fl w)) cw hK
    (fun F => ⟨differentiableOn_of_hasSum _ _ _ fun w hw => (hcw w hw F.1 F.2).1,
      (hU.2.2.2.2.1 a' n hD F.1 F.2 k).1.comp hfl.differentiableOn
        fun w hw => (hflow w (max_lt_iff.1 hw).1).1⟩)
    (fun F w hw => ⟨rfl, (hcw w hw F.1 F.2).2⟩)
  refine ⟨⟨x, hx⟩, κ, L, γ, fun v => ?_, hEF, hLz, ⟨t, ht, htξ⟩, hκ, fun F hF hbdd => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hflow w₁ hw₁
    rw [← h2 v]
    congr 3
    simp only [sub_self, zero_mul]
    exact (EmbeddingHermitianPairs.flow_zero _ _ _).symm
  · refine coeff_eq_of_betaAt (U.X k) hbdd hiso hx ξ l.M' a.be
      (fun y z => (dvd_mul_left _ 2).trans (a.be_dvd y z)) hβ hbe hpos (hTr k) (hlev _) κ w₁ _ (max Ha.T T')
      fun w hw => ?_
    exact hκ' ⟨F, hF⟩ w hw ▸ (hcw w hw F hF).1

end GlobalTheory.ArcCoeff
end
