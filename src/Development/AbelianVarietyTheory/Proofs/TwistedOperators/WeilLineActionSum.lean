import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroupStatement
import BuildAid.ForwardExisting
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergLine_derivative_formula : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ ∀ f g : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) ⇑f ⇑g → ∀ y, g y =
        fderiv ℝ (⇑f) y v.1 - 2 * Real.pi * Complex.I * (trP F (Fin n × Fin d) y v.2 : ℂ) * f y := by
  first | exact @GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq | exact GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq | (intros; apply GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq <;> assumption)
end

section
section
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hE : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2))
        (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y := by
    intro y
    exact ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp
  have hu : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
        (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y := by
    intro y
    have h1 := (hE y).smul (h.differentiableAt (x := y)).hasFDerivAt
    refine h1.congr_fderiv ?_
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun l ℝ).toBasis.ext
    intro j
    have h2 := H j y
    have h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y) :=
      eq_neg_of_add_eq_zero_left h2
    simp [h3, EuclideanSpace.inner_single_right]
    ring
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
    (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, one_smul] at hc
  rw [← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end GlobalTheory
end

open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' : ∀ (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ)), (∀ (j : l) (x : EuclideanSpace ℝ l), fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0) → ∀ x, h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  atlas_forward_decl GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero
end

section
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

open scoped FourierTransform RealInnerProductSpace Real

namespace GlobalTheory.RealWeil

theorem eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by
  intro l _ k h
  set G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  let m : EuclideanSpace ℝ l → ℂ := fun x => G x * k x
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith [sq_nonneg ‖x‖]
  have hm_cont : Continuous m := G.continuous.mul k.continuous
  have hm_int : Integrable m := k.integrable.norm.mono' hm_cont.aestronglyMeasurable
    (ae_of_all _ fun x => by
      simp only [m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hGn x))
  have hF : 𝓕 m = 0 := by
    funext q
    have hq := h (Sum.elim 0 (fun i => q i))
    have hp : pPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = 0 := by
      ext i; simp [pPart]
    have hqq : qPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = q := by
      ext i; simp [qPart]
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume] at hq
    rw [Real.fourier_eq', Pi.zero_apply, ← hq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [m, coe_rhoSch, rhoFun, phase, hp, hqq, add_zero, inner_zero_left, mul_zero, RCLike.inner_apply,
      map_mul, smul_eq_mul]
    rw [← Complex.exp_conj]
    have hGc : (starRingEnd ℂ) (G x) = G x := by
      rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [hGc]
    have : (starRingEnd ℂ) (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * Complex.I) =
        ((-2 * π * ⟪x, q⟫ : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, real_inner_comm]
      push_cast
      ring
    rw [this]
    ring
  have hm0 : m = 0 := by
    have hi : Integrable (𝓕 m) := by rw [hF]; exact integrable_zero _ _ _
    rw [← hm_cont.fourierInv_fourier_eq hm_int hi, hF]
    funext v
    simp [Real.fourierInv_eq]
  ext x
  have hx := congrFun hm0 x
  simp only [m, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exfalso
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).ne' hx
  · simpa using hx

end GlobalTheory.RealWeil
end

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  atlas_forward_decl GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian
end

section
section
noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

theorem fderiv_gaussianSchwartz_single_add {l : Type} [Fintype l] [DecidableEq l] (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) =
      (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem inner_toLp_map_of_integral_norm_sq : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    ∀ f g, inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  intro l _ S hiso f g
  set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU
  have hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖ := by
    intro h
    simp only [hU, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [hiso]
  have e1 : (S f).toLp 2 volume = U (S f) := rfl
  have e2 : (S g).toLp 2 volume = U (S g) := rfl
  have e3 : f.toLp 2 volume = U f := rfl
  have e4 : g.toLp 2 volume = U g := rfl
  rw [e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, hn]

theorem exists_eq_smul_of_commute_rhoFun : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  intro l _ S hiso hcomm
  classical
  have hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    rw [ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num))
      (.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    intro f
    rw [one_mul, hl, hl, hiso]
  have hd := GlobalTheory.T.derived_action_intertwines_of_group l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)
  set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  have hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x =
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x := by
    intro j h x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring
  have hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * S G x = 0 := by
    intro j x
    have h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0 := by
      ext y
      rw [hN, hG, fderiv_gaussianSchwartz_single_add]
      rfl
    have := congrArg S h0
    rw [map_sub, map_smul, hd, hd, map_zero] at this
    rw [← hN, LinearMap.id_apply, LinearMap.id_apply] at *
    rw [this]
    rfl
  set c : ℂ := S G 0 with hc
  have hSGc : S G = c • G := by
    ext x
    rw [GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]
  have hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G := by
    intro w
    ext x
    rw [hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]
    simp only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f := by
    intro f
    rw [← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian l
    intro w
    have hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume := fun a g =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g
    have hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume := fun g g' =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'
    have hp := inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f
    rw [hrho, hsm, inner_smul_left] at hp
    rw [hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]
  have hc0 : starRingEnd ℂ c ≠ 0 := by
    intro h0
    have := congrArg (fun g : Sch l => g 0) (key G)
    simp [h0, hG] at this
  exact ⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩

end GlobalTheory.RealWeil
end
end

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l), (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  atlas_forward_decl GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun
end

section
section
namespace GlobalTheory

theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  intro lam h0 hmul hc
  have hcont : Continuous lam := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun x => lam (x - t)) t := by
      apply ContinuousAt.comp (g := lam) (f := fun x => x - t)
      · simpa using hc
      · exact (continuous_id.sub continuous_const).continuousAt
    have h2 : (fun x => lam t * lam (x - t)) = lam := by
      funext x; rw [← hmul]; congr 1; ring
    rw [← h2]; exact continuousAt_const.mul h1
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF
  have hFd : ∀ b, HasDerivAt F (lam b) b := fun b =>
    (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    have := (hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    exact this.exists
  have hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have key : ∀ t, lam t * F δ = F (t + δ) - F t := by
    intro t
    calc lam t * F δ = ∫ s in (0:ℝ)..δ, lam (t + s) := by
          simp only [hF, hmul]; rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t
      _ = F (t + δ) - F t := by
          simp only [add_zero, hF]
          exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹)
      ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0 := by
    have h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0 :=
      HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))
    exact (h1.sub (hFd 0)).mul_const _
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
  simp only
  rw [← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add : ∀ (lam : ℝ → ℂ), lam 0 = 1 → (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  atlas_forward_decl GlobalTheory.multiplicative_hasDerivAt_zero
end

section
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
end

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  atlas_forward_decl GlobalTheory.famChar_hasDerivAt
end

section
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory.RealWeil

theorem integral_norm_sq_eq_norm_toLp_sq {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem metaplectic_oneParam_schwartz : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this

end GlobalTheory.RealWeil

end
end

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧ (∀ f, U 0 f = f) ∧ (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧ (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  atlas_forward_decl GlobalTheory.RealWeil.metaplectic_oneParam_schwartz
end

section
open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @GlobalTheory.ArchUniq.SchrTransport.transport | exact GlobalTheory.ArchUniq.SchrTransport.transport | (intros; apply GlobalTheory.ArchUniq.SchrTransport.transport <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical Matrix

namespace GlobalTheory.QuadFam

open GlobalTheory.RealWeil

theorem coordAll (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∃ (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℂ), ∀ f y, HasDerivAt (fun t => T t f y) (quad X f y + c * f y) 0 := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  cases isEmpty_or_nonempty l with
  | inl hl =>
    have hq : ∀ f y, quad (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) f y = 0 := fun f y => by simp [quad]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T (fun _ => LinearMap.id) (fun f y => quad 0 f y) hT hT0
      (fun _ _ _ => rfl) (fun _ => rfl) hgrp h0 hI
      (fun t w f f₁ h => by
        rw [LinearMap.id_apply, LinearMap.id_apply, h, Subsingleton.elim (A t w) w]) hiso
      (fun _ _ => rfl) hpt (fun f y => by rw [hq]; exact hasDerivAt_const _ _)
    exact ⟨0, c, hc⟩
  | inr hl =>
    let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
    have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
    have hMc : Continuous M := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [M, LinearMap.toMatrix'_apply]
      exact (continuous_apply i).comp (hA _)
    have hM0 : M 0 = 1 := by
      have : A 0 = LinearMap.id := LinearMap.ext h0
      simp only [M, this, LinearMap.toMatrix'_id]
    have hMm : ∀ s t, M (s + t) = M s * M t := by
      intro s t
      have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
      simp only [M, this, LinearMap.toMatrix'_comp]
    obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
    have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
      refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
      obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
      have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
        rw [Matrix.toLin'_apply, hN]
      have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
        simp only [M, ← e, LinearMap.toMatrix'_toLin']
      rw [← hX t, ← e2]
      exact N.2
    obtain ⟨U, hU, hU0, hUI, hUiso, hUd⟩ := GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining hP l X hsp
    have hB : ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := fun t w => by rw [← hX, hM]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T U (fun f y => quad X f y) hT hT0 hU hU0 hgrp h0 hI
      (fun t w f f₁ h => by rw [hUI t w f f₁ h, hB]) hiso hUiso hpt hUd
    exact ⟨X, c, hc⟩

theorem deriv_quad : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro hP V _ _ _ _ _ μ hμ P hp A T hA hT hT0 hI hiso hpt _
  exact GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates V μ hμ P hp _ rfl (fun A' T' => coordAll hP (Fin _) A' T') A T hA hT hT0 hI hiso hpt

end GlobalTheory.QuadFam
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMetaplectic_family_derivative_quadratic : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  atlas_forward_decl GlobalTheory.QuadFam.deriv_quad
end

section
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory

namespace GlobalTheory.OscQuad

theorem deriv_line_quad : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨T, hT, hadd, h0⟩ := GlobalTheory.T.weil_line_one_parameter hP M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  obtain ⟨m, a, b, c, c₀, hR⟩ := GlobalTheory.T.realMetaplectic_family_derivative_quadratic hP.realMetaplecticRepresentation
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ inferInstance _
    (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T hAc hadd h0 hA hiso hc1 (hc2 μ inferInstance)
  choose u hu hDu using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (a i)
  choose v hv hDv using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (b i)
  obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  refine ⟨m, u, v, c, c₀, fun i => ⟨hu i, hv i⟩, ?_⟩
  intro f g₁ g₂ h1 h2 F₁ hF y
  have eF : ∀ t, F₁ t = T t f := fun t => hinj _ _ ((hF t r₀ (hr₀ f)).symm.trans (hT t f r₀ (hr₀ f)))
  simp only [eF]
  exact hR f g₁ g₂ (fun i y => hDv i f (g₁ i) (h1 i) y) (fun i y => hDu i (g₁ i) (g₂ i) (h2 i) y) y

end GlobalTheory.OscQuad

end
end
