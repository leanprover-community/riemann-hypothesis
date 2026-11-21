import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.HeisDeriv
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem hasDerivAt_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) (pureA F f g) x)
      (pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g x) 0 := by
  set v : κ → mixedEmbedding.mixedSpace F := fun i => evI F (w.1 i) with hv
  set z : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F w.2 z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) with hQ
  have hline : ∀ t : ℝ, schr ψ (realAd F t • w) (pureA F f g) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) *
        (f (z + t • v) * g (fun i => (x i).2)) := by
    intro t
    simp only [schr, Prod.smul_fst, Prod.smul_snd]
    set A : AF F := x ⬝ᵥ (realAd F t • w.2) + ⅟(2 : AF F) * ((realAd F t • w.1) ⬝ᵥ (realAd F t • w.2)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ w.2) = ∑ i, z i * evI F (w.2 i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • w.1) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    have hfin : (fun i => ((x + realAd F t • w.1) i).2) = fun i => (x i).2 := by
      funext i
      show (x i).2 + (realAd F t).2 * (w.1 i).2 = (x i).2
      rw [show (realAd F t).2 = 0 from rfl, zero_mul, add_zero]
    rw [hψ.2.2 A hAt2, htr]
    show _ * (f (fun i => evI F ((x + realAd F t • w.1) i)) * g (fun i => ((x + realAd F t • w.1) i).2)) = _
    rw [harg, hfin]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (g (fun i => (x i).2)))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  show _ = heisD F v w.2 f z * g (fun i => (x i).2)
  simp only [heisD_apply, mult_apply, ← hP]
  simp
  ring

theorem exists_hasDerivAt (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) :
    ∃ Φ' ∈ schA F κ, ∀ x, HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) Φ x) (Φ' x) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ⟨pureA F (heisD F (fun i => evI F (w.1 i)) w.2 f) g, Submodule.subset_span ⟨_, g, hg, rfl⟩,
      fun x => hasDerivAt_pureA ψ hψ w f g x⟩
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    refine (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.zero_apply, mul_zero]
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨Φ₁', m₁, d₁⟩ := h₁
    obtain ⟨Φ₂', m₂, d₂⟩ := h₂
    refine ⟨Φ₁' + Φ₂', add_mem m₁ m₂, fun x => ?_⟩
    refine ((d₁ x).add (d₂ x)).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.add_apply, mul_add]
  | smul a Φ _ h =>
    obtain ⟨Φ', m, d⟩ := h
    refine ⟨a • Φ', Submodule.smul_mem _ a m, fun x => ?_⟩
    refine ((d x).const_mul a).congr_of_eventuallyEq (.of_forall fun t => ?_)
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.ThetaDecay.DHMem

open GlobalTheory.ThetaDecay.DHMem in

theorem GlobalTheory.ThetaDecay.dH_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ w : (κ → AF F) × (κ → AF F), IsArch w → ∀ Φ ∈ schA F κ, dH ψ w Φ ∈ schA F κ := by
  intro F _ _ κ _ ψ hψ w _ Φ hΦ
  obtain ⟨Φ', hΦ', hd⟩ := exists_hasDerivAt ψ hψ w Φ hΦ
  have : dH ψ w Φ = Φ' := funext fun x => (hd x).deriv
  rw [this]
  exact hΦ'

end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ w : (κ → AF F) × (κ → AF F), IsArch w → ∀ Φ ∈ schA F κ, dH ψ w Φ ∈ schA F κ := by
  first | exact @GlobalTheory.ThetaDecay.dH_mem_schA | exact GlobalTheory.ThetaDecay.dH_mem_schA | (intros; apply GlobalTheory.ThetaDecay.dH_mem_schA <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.SliceSob

section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def dw (l : List V) (g : V → ℂ) : V → ℂ :=
  l.foldr (fun e u y => fderiv ℝ u y e) g

theorem contDiff_dw (l : List V) {g : V → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (dw l g) := by
  induction l with
  | nil => exact hg
  | cons e l ih =>
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_line {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) (t : ℝ) :
    HasDerivAt (fun r : ℝ => u (x + r • e)) (fderiv ℝ u (x + t • e) e) t := by
  have h1 : HasDerivAt (fun r : ℝ => x + r • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  exact ((hu.differentiable (by simp)) (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1

theorem step {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) :
    ‖u x‖ ^ 2 ≤ (2 * ∫ r in (0:ℝ)..1, ‖u (x + r • e)‖ ^ 2) +
      2 * ∫ r in (0:ℝ)..1, ‖fderiv ℝ u (x + r • e) e‖ ^ 2 := by
  have hc : Continuous (dw [e] u) := (contDiff_dw [e] hu).continuous
  have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun r : ℝ => u (x + r • e))
    (fun r : ℝ => fderiv ℝ u (x + r • e) e) 1 one_pos (fun t _ => hasDerivAt_line hu x e t)
    (hc.comp (f := fun r : ℝ => x + r • e) (by fun_prop)).continuousOn
  simpa using this

theorem sobolev_haar [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {D : ℕ} (b : Module.Basis (Fin D) ℝ V) :
    ∃ C : ℝ, ∀ g : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ S : ENNReal,
      (∀ l : List (Fin D), l.length ≤ D → ∫⁻ y, ‖dw (l.map b) g y‖ₑ ^ 2 ∂μ ≤ S) →
      ‖g 0‖ₑ ^ 2 ≤ ENNReal.ofReal C * S := by
  let T : (Fin D → ℝ) ≃L[ℝ] V := b.equivFunL.symm
  have hT : ∀ t, T t = ∑ i, t i • b i := fun t => b.equivFun_symm_apply t
  let ν : Measure V := Measure.map T volume
  haveI : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map _
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  refine ⟨4 ^ D * (c + 1), fun g hg S hS => ?_⟩
  have hpos : (0:ℝ) < 4 ^ D * (c + 1) := by positivity
  rcases eq_or_ne S ⊤ with rfl | hS'
  · rw [ENNReal.mul_top (by simpa using hpos)]; exact le_top
  have key := GlobalTheory.ThetaGrowth.sobolev_iter D 0 (fun i r => r • b i)
    (fun p => {u | ∃ l : List (Fin D), l.length ≤ p ∧ u = dw (l.map b) g}) (c * S.toReal) (0 : V)
    (fun i => by fun_prop)
    (fun p q hpq u ⟨l, hl, hu⟩ => ⟨l, hl.trans hpq, hu⟩)
    (by
      rintro p u ⟨l, hl, rfl⟩
      refine ⟨(contDiff_dw _ hg).continuous, fun i => ⟨dw ((i :: l).map b) g,
        ⟨i :: l, by simpa using hl, rfl⟩, fun x => ?_⟩⟩
      exact step (contDiff_dw _ hg) x (b i))
    (by
      rintro u ⟨l, hl, rfl⟩
      have hcu : Continuous (dw (l.map b) g) := (contDiff_dw _ hg).continuous
      have h1 := hS l (by simpa using hl)
      set u := dw (l.map b) g
      simp only [zero_add, ← hT]
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
        (Continuous.aestronglyMeasurable (by fun_prop))]
      have h2 : ∫⁻ t in Set.univ.pi fun _ => Set.Icc (0:ℝ) 1, ENNReal.ofReal (‖u (T t)‖ ^ 2)
          ≤ c * S := by
        calc _ ≤ ∫⁻ t, ENNReal.ofReal (‖u (T t)‖ ^ 2) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ t, ‖u (T t)‖ₑ ^ 2 := by
            refine lintegral_congr fun t => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          _ = ∫⁻ y, ‖u y‖ₑ ^ 2 ∂ν := by
            rw [lintegral_map (hcu.measurable.enorm.pow_const 2) T.continuous.measurable]
          _ = c * ∫⁻ y, ‖u y‖ₑ ^ 2 ∂μ := by
            rw [hν, lintegral_smul_measure]; rfl
          _ ≤ c * S := by gcongr
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hS') h2
      simpa using this)
    g ⟨[], le_rfl, rfl⟩
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_toReal hS', ← ENNReal.ofReal_mul hpos.le]
  refine ENNReal.ofReal_le_ofReal (key.trans ?_)
  rw [mul_assoc]
  gcongr
  linarith

theorem exists_small_basis [FiniteDimensional ℝ V] :
    ∃ (D : ℕ) (b : Module.Basis (Fin D) ℝ V), ∀ i, ‖b i‖ ≤ 1 := by
  let b := Module.finBasis ℝ V
  have h : ∀ i, (‖b i‖⁻¹ : ℝ) ≠ 0 := fun i => inv_ne_zero (norm_ne_zero_iff.2 (b.ne_zero i))
  refine ⟨_, b.unitsSMul fun i => Units.mk0 _ (h i), fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (b.ne_zero i))]

end General

open GlobalTheory.SobClass

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem contDiff_slice {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → AF F) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    have e : (fun y => pureA F f g (x + archInc F y)) = fun y =>
        f ((fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1) + y) *
          g (fun i => (x i).2) := by
      funext y
      unfold pureA
      congr 2
      · funext i
        change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 +
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = _
        rw [map_add, RingEquiv.apply_symm_apply]; rfl
      · funext i
        change (x i).2 + (archInc F y i).2 = _
        rw [archInc_snd, add_zero]
    rw [e]
    exact ((f.smooth ⊤).comp (contDiff_const.add contDiff_id)).mul contDiff_const
  | zero => exact contDiff_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact contDiff_const.mul h

theorem realAd_smul_archInc (t : ℝ) (e : κ → mixedEmbedding.mixedSpace F) :
    realAd F t • archInc F e = archInc F (t • e) := by
  funext i
  refine Prod.ext ?_ ?_
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (e i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e i)
    rw [← map_mul, Algebra.smul_def]
  · change (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    rw [mul_zero]

theorem word_slice (ψ : AddChar (AF F) ℂ) {Φ : (κ → AF F) → ℂ} (x : κ → AF F)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y))
    (l : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun y => wordH ψ (l.map fun e => (archInc F e, 0)) Φ (x + archInc F y)) =
      dw l fun y => Φ (x + archInc F y) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    funext y
    have h := (hasDerivAt_line (contDiff_dw l hΦ) y e 0).deriv
    rw [zero_smul, add_zero] at h
    refine Eq.trans ?_ h
    change deriv (fun t : ℝ => schr ψ (realAd F t • (archInc F e, 0))
      (wordH ψ (l.map fun e => (archInc F e, 0)) Φ) (x + archInc F y)) 0 = _
    congr 1
    funext t
    rw [← ih]
    simp only [schr, Prod.smul_mk, smul_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul, realAd_smul_archInc, archInc_add, add_assoc]

theorem slice_sobolev : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (D : ℕ) (C : ℝ), (∀ l ∈ L, l.length ≤ D ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ Φ ∈ schA F κ, ∀ x : κ → AF F, ‖Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ l ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + GlobalTheory.SobClass.archInc F y)‖ₑ ^ 2 := by
  intro F _ _ κ _ ψ _
  obtain ⟨D, b, hb⟩ := exists_small_basis (V := κ → mixedEmbedding.mixedSpace F)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  obtain ⟨C, hC⟩ := sobolev_haar (volume : Measure (κ → mixedEmbedding.mixedSpace F)) b
  let L₀ : Finset (List (Fin D)) := (List.finite_length_le (Fin D) D).toFinset
  refine ⟨L₀.image fun l => (l.map b).map fun e => (archInc F e, 0), D, C, ?_, ?_⟩
  · intro l hl
    obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
    refine ⟨by simpa [L₀] using hl', fun w hw => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact isArchUnit_der _ fun i => (norm_le_pi_norm _ i).trans (hb j)
  · intro Φ hΦ x
    have h0 : archInc F (0 : κ → mixedEmbedding.mixedSpace F) = 0 := by
      have := archInc_add (F := F) (κ := κ) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    have := hC _ (contDiff_slice hΦ x) (∑ l ∈ L₀.image fun l => (l.map b).map
        fun e => ((archInc F e, 0) : (κ → AF F) × (κ → AF F)),
        ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2)
      (fun l hl => by
        rw [← word_slice ψ x (contDiff_slice hΦ x)]
        exact Finset.single_le_sum (f := fun l => ∫⁻ y : κ → mixedEmbedding.mixedSpace F,
          ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2) (fun _ _ => zero_le)
          (Finset.mem_image_of_mem _ (by simpa [L₀] using hl)))
    simpa only [h0, add_zero] using this

end GlobalTheory.SliceSob
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_pointwise_bound_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (D : ℕ) (C : ℝ), (∀ l ∈ L, l.length ≤ D ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ Φ ∈ schA F κ, ∀ x : κ → AF F, ‖Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ l ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + GlobalTheory.SobClass.archInc F y)‖ₑ ^ 2 := by
  atlas_forward_decl GlobalTheory.SliceSob.slice_sobolev
end

section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.ClassMeas

theorem slice_le {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [T2Space V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (ν₀ : Measure V) [ν₀.IsAddHaarMeasure]
    (ι : V →+ G) (π : G →+ V) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) {K : Set G}
    (hK : IsCompact K) (h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : G)) :
    ∃ c : NNReal, ∀ (J : Type) [Fintype J] (t : J → G) (K' : Set G), IsCompact K' → (∀ k ∈ K, ∃ j, k - t j ∈ K') →
      ∀ f : G → ENNReal, (∀ x, ∀ k ∈ K', f (x + k) = f x) → ∀ x, Measurable (fun y => f (x + ι y)) →
        ∫⁻ y, f (x + ι y) ∂ν₀ ≤ c * (Fintype.card J * ∫⁻ w, f w ∂μ) := by
  set W : Set G := {w | w - ι (π w) ∈ K} with hW
  have hp : Continuous fun w => w - ι (π w) := continuous_id.sub (hι.comp hπ)
  have hV : MeasurableSet W := (hK.isClosed.preimage hp).measurableSet
  have hsub : ∀ B : Set V, π ⁻¹' B ∩ W ⊆ (fun p : G × V => p.1 + ι p.2) '' (K ×ˢ B) := fun B w hw =>
    ⟨(_, _), ⟨hw.2, hw.1⟩, sub_add_cancel _ _⟩
  let ν : Measure V := (μ.restrict W).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ W) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact (measure_mono (hsub A)).trans_lt
      ((hK.prod hA).image (continuous_fst.add (hι.comp continuous_snd))).measure_lt_top⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ W)]
    congr 1
    ext w
    simp only [hW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • ν₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul ν ν₀⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hν Set.univ MeasurableSet.univ
    rw [hc, zero_smul, Set.preimage_univ, Set.univ_inter] at h1
    exact (Measure.measure_pos_of_mem_nhds μ h0).ne h1
  refine ⟨c⁻¹, fun J _ t K' hK' hcov f hf x hm => ?_⟩
  have e1 : ∫⁻ y, f (x + ι y) ∂ν = c * ∫⁻ y, f (x + ι y) ∂ν₀ := by
    rw [hc, lintegral_smul_measure]; rfl
  have e2 : ∫⁻ y, f (x + ι y) ∂ν ≤ Fintype.card J * ∫⁻ w, f w ∂μ := by
    let S : J → Set G := fun j => {w | w - ι (π w) - t j ∈ K'}
    have hS : ∀ j, MeasurableSet (S j) := fun j =>
      (hK'.isClosed.preimage (hp.sub continuous_const)).measurableSet
    have hWS : W ⊆ ⋃ j, S j := fun w hw => Set.mem_iUnion.2 (hcov _ hw)
    rw [lintegral_map hm hπ.measurable]
    refine (lintegral_mono_set hWS).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
    rw [setLIntegral_congr_fun (g := fun w => f (x - t j + w)) (hS j) (fun w hw => by
      show f (x + ι (π w)) = f (x - t j + w)
      rw [← hf _ _ hw]
      congr 1
      abel)]
    exact (setLIntegral_le_lintegral _ _).trans (lintegral_add_left_eq_self f _).le
  rw [e1] at e2
  rw [ENNReal.coe_inv hc0]
  exact (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top).1 e2

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem isOpen_int : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem card_quot (m : ℕ) : Nat.card (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap]
  simp

theorem exists_rep (m : ℕ) (hm : 1 ≤ m) (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ (q : 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) (b : FiniteAdeleRing (𝓞 F) F), (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) q.out = m * b := by
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (m : 𝓞 F) (by exact_mod_cast (by omega : m ≠ 0)) a ha
  obtain ⟨s, hs⟩ : ∃ s, s * (m : 𝓞 F) = r - (Ideal.Quotient.mk (Ideal.span {(m : 𝓞 F)}) r).out := by
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    exact (Quotient.out_eq _).symm
  refine ⟨Ideal.Quotient.mk _ r, y + algebraMap (𝓞 F) _ s, fun v => add_mem (hy v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v s), ?_⟩
  have := congrArg (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) hs
  rw [map_mul, map_sub, map_natCast] at this
  rw [map_natCast] at e
  rw [e]
  linear_combination -this

theorem class_meas : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := t2Space_adeleRing_of_numberField F
  refine ⟨Measure.addHaar, inferInstance, ?_⟩
  let ι : (κ → mixedEmbedding.mixedSpace F) →+ (κ → AF F) := AddMonoidHom.mk' (archInc F) archInc_add
  let π : (κ → AF F) →+ (κ → mixedEmbedding.mixedSpace F) := AddMonoidHom.mk' (fun z i => evI F (z i))
    (fun z z' => funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1 (z' i).1)
  have hι : Continuous ι := continuous_pi fun i =>
    Continuous.prodMk ((continuous_ofMixed F).comp (continuous_apply i)) continuous_const
  have hπ : Continuous π := continuous_pi fun i =>
    (continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hπι : ∀ y, π (ι y) = y := fun y => funext fun i => evI_archInc y i
  let I : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  let K : Set (κ → AF F) := Set.pi Set.univ fun _ => (({0} : Set (Ainf F)) ×ˢ I : Set (Ainf F × Af F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_singleton.prod (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : κ → AF F) := by
    have ho : IsOpen (Set.pi Set.univ fun _ : κ => {a : AF F | a.2 ∈ I}) :=
      isOpen_set_pi Set.finite_univ fun _ _ => (isOpen_int F).preimage continuous_snd
    refine mem_of_superset (ho.mem_nhds fun i _ v => zero_mem _) fun w hw i _ => ⟨?_, ?_⟩
    · show (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1) = 0
      rw [RingEquiv.symm_apply_apply, sub_self]
    · show (w i).2 - 0 ∈ I
      rw [sub_zero]
      exact hw i trivial
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ := slice_le (Measure.addHaar : Measure (κ → AF F)) volume ι π hι hπ hπι hK h0
  refine ⟨Module.finrank ℤ (𝓞 F) * Fintype.card κ, c, fun m hm f hf x hx => ?_⟩
  have hcard := card_quot F m
  haveI : Finite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
  have key := hc (κ → 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
    (fun q i => pairA F 0 (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (q i).out)) ((fun a => (m : AF F) • a) '' K)
    (hK.image (continuous_const_smul _)) ?_ f ?_ x hx
  · rw [Fintype.card_fun, ← Nat.card_eq_fintype_card, hcard, ← pow_mul, ← mul_assoc] at key
    refine key.trans (le_of_eq ?_)
    congr 1
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  · intro k hk
    choose q b hb e using fun i => exists_rep F m hm (k i).2 (hk i trivial).2
    refine ⟨q, fun i => pairA F 0 (b i), fun i _ => ⟨rfl, hb i⟩, funext fun i => Prod.ext ?_ (e i).symm⟩
    have : (k i).1 = 0 := (hk i trivial).1
    show ((m : AF F)).1 * 0 = (k i).1 - 0
    rw [this, mul_zero, sub_zero]
  · rintro z _ ⟨a, ha, rfl⟩
    refine hf z a fun i => ⟨?_, (ha i trivial).2⟩
    have : (a i).1 = 0 := (ha i trivial).1
    rw [evI, this, map_zero]

end GlobalTheory.SobClass.ClassMeas
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_periodic_arch_restriction : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  atlas_forward_decl GlobalTheory.SobClass.ClassMeas.class_meas
end

section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.Weight
open GlobalTheory.SobClass GlobalTheory.ArchUniq.Coord

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem norm_dH_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (i : κ) (e : mixedEmbedding.mixedSpace F)
    (Φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    ‖dH ψ ((0, archInc F (Pi.single i e)) : (κ → AF F) × (κ → AF F)) Φ z‖ =
      2 * Real.pi * |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e)| * ‖Φ z‖ := by
  set T : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e) with hT
  set a : κ → AF F := archInc F (Pi.single i e) with ha
  have key : (fun t : ℝ => schr ψ (realAd F t • ((0, a) : (κ → AF F) × (κ → AF F))) Φ z) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z := by
    funext t
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero]
    have hA : At (evI F) (z ⬝ᵥ (realAd F t • a)) := by
      intro u hu
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := at_archInc (Pi.single i e) j u hu
      simp only [smul_eq_mul] at this
      calc _ = z j * realAd F t * (u * archInc F (Pi.single i e) j) := by rw [ha]; ring
        _ = 0 := by rw [this, mul_zero]
    have hE : evI F (z ⬝ᵥ (realAd F t • a)) = t • (evI F (z i) * e) := by
      rw [evI_eq]
      simp only [dotProduct, smul_eq_mul, Pi.smul_apply, map_sum, map_mul, ← evI_eq, evI_realAd, ha, evI_archInc]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, Algebra.smul_def]
      ring
    rw [hψ.2.2 _ hA, hE, map_smul, ← hT, smul_eq_mul]
    congr 2
    push_cast
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * T * t) * Φ z)
      (Complex.exp (-(2 * Real.pi * Complex.I) * T * ((0 : ℝ) : ℂ)) * (-(2 * Real.pi * Complex.I) * T * 1) * Φ z) 0 :=
    (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-(2 * Real.pi * Complex.I) * T)).cexp).mul_const (Φ z)
  unfold dH
  rw [key, hd.deriv]
  simp [abs_of_pos Real.pi_pos]

variable (F) in
theorem exists_family : ∃ (n : ℕ) (e : Fin n → mixedEmbedding.mixedSpace F) (c : ℝ), 0 ≤ c ∧ (∀ j, ‖e j‖ ≤ 1) ∧
    ∀ x : mixedEmbedding.mixedSpace F, ‖x‖ ≤ c * ∑ j, |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)| := by
  let b := Module.finBasis ℝ (mixedEmbedding.mixedSpace F)
  let e : Fin _ → mixedEmbedding.mixedSpace F := fun j => (1 + ‖b j‖)⁻¹ • b j
  have hp : ∀ j, 0 < 1 + ‖b j‖ := fun j => by positivity
  let f : mixedEmbedding.mixedSpace F →ₗ[ℝ] (Fin _ → ℝ) :=
    LinearMap.pi fun j => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ∘ₗ LinearMap.mulRight ℝ (e j)
  have hf : ∀ x j, f x j = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j) := fun x j => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => eq_zero_of_trace x fun y => ?_
    have h1 : ∀ j, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b j) = 0 := by
      intro j
      have := hf x j
      rw [hx, Pi.zero_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (inv_pos.2 (hp j)).ne'
    rw [← b.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, h1, smul_zero]
  obtain ⟨K, -, hK⟩ := f.exists_antilipschitzWith hker
  refine ⟨_, e, K, K.2, fun j => ?_, fun x => ?_⟩
  · simp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hp j)), inv_mul_le_iff₀ (hp j)]
    linarith
  · refine (ZeroHomClass.bound_of_antilipschitz f hK x).trans (mul_le_mul_of_nonneg_left ?_ K.2)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
    rw [hf, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * e j)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j)

theorem weight_le_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ N : ℕ, ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F), ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ := by
  intro F _ _ κ _ ψ hψ N
  obtain ⟨n, e, c, hc, he, hx⟩ := exists_family F
  let m : κ × Fin n → (κ → AF F) × (κ → AF F) := fun p => (0, archInc F (Pi.single p.1 (e p.2)))
  have hm : ∀ p, IsArchUnit (m p) := fun p => isArchUnit_mul _ fun i => by
    by_cases h : i = p.1
    · subst h; simpa using he p.2
    · simp [h]
  have hw : ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * ∑ i, ‖evI F (z i)‖ ≤ c * ∑ p, ‖dH ψ (m p) Φ z‖ := by
    intro Φ z
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hc
    simp only [m]
    rw [norm_dH_mul hψ]
    have h1 := mul_nonneg (norm_nonneg (Φ z))
      (abs_nonneg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z i) * e j)))
    nlinarith [Real.two_le_pi]
  suffices h : ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), 0 ≤ K ∧
      (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F),
      ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ by
    obtain ⟨L, K, -, h⟩ := h
    exact ⟨L, K, h⟩
  induction N with
  | zero => exact ⟨{[]}, 1, zero_le_one, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨L, K, hK, hL, h⟩ := ih
    let L' := L ∪ Finset.univ.biUnion fun p => L.image (List.cons (m p))
    refine ⟨L', K * (1 + c * Fintype.card (κ × Fin n)), by positivity, fun l hl => ?_, fun Φ z => ?_⟩
    · rcases Finset.mem_union.1 hl with hl | hl
      · exact ⟨(hL l hl).1.trans (Nat.le_succ _), (hL l hl).2⟩
      · obtain ⟨p, -, hl⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
        refine ⟨by simpa using (hL l hl').1, fun w hw => ?_⟩
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hm p
        · exact (hL l hl').2 w hw
    · set S := ∑ l ∈ L', ‖wordH ψ l Φ z‖ with hS
      have h1 : ∑ l ∈ L, ‖wordH ψ l Φ z‖ ≤ S :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => norm_nonneg _
      have h2 : ∀ p, ∑ l ∈ L, ‖dH ψ (m p) (wordH ψ l Φ) z‖ ≤ S := by
        intro p
        have := Finset.sum_image (s := L) (g := List.cons (m p)) (f := fun l => ‖wordH ψ l Φ z‖)
          (fun _ _ _ _ h => List.cons_injective h)
        simp only [wordH_cons] at this
        rw [← this]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => Finset.mem_union_right _ ?_)
          fun _ _ _ => norm_nonneg _
        exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hl⟩
      have h3 : (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖ ≤ c * (Fintype.card (κ × Fin n) * S) := by
        rw [Finset.sum_mul]
        refine (Finset.sum_le_sum fun l _ => hw (wordH ψ l Φ) z).trans ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun p _ => h2 p).trans ?_) hc
        simp
      have h0 : 0 ≤ 1 + ∑ i, ‖evI F (z i)‖ := by positivity
      calc _ = (‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N) * (1 + ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ (K * ∑ l ∈ L, ‖wordH ψ l Φ z‖) * (1 + ∑ i, ‖evI F (z i)‖) := mul_le_mul_of_nonneg_right (h Φ z) h0
        _ = K * (∑ l ∈ L, ‖wordH ψ l Φ z‖ + (∑ l ∈ L, ‖wordH ψ l Φ z‖) * ∑ i, ‖evI F (z i)‖) := by ring
        _ ≤ K * (S + c * (Fintype.card (κ × Fin n) * S)) := mul_le_mul_of_nonneg_left (add_le_add h1 h3) hK
        _ = _ := by ring

end GlobalTheory.SobClass.Weight
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_polynomial_decay_words : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ N : ℕ, ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (K : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ (Φ : (κ → AF F) → ℂ) (z : κ → AF F), ‖Φ z‖ * (1 + ∑ i, ‖evI F (z i)‖) ^ N ≤ K * ∑ l ∈ L, ‖wordH ψ l Φ z‖ := by
  atlas_forward_decl GlobalTheory.SobClass.Weight.weight_le_words
end

section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass

theorem wordH_mem_sch {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.T.heisenberg_derivative_preserves_schwartz F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

theorem sqrt_bound (Q M B t : ℝ) (hQ : 0 ≤ Q) (hM : 1 ≤ M) (hB : 0 ≤ B) (ht : 0 ≤ t) (h : t ^ 2 ≤ Q * (M * B)) :
    t ≤ √Q * (M * (1 + B)) := by
  have h1 : M * B ≤ (M * (1 + B)) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hM) hB]
  have h2 : t ≤ √(Q * (M * B)) := Real.le_sqrt_of_sq_le h
  calc t ≤ √(Q * (M * B)) := h2
    _ = √Q * √(M * B) := Real.sqrt_mul hQ _
    _ ≤ √Q * (M * (1 + B)) := by
        gcongr
        calc √(M * B) ≤ √((M * (1 + B)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = M * (1 + B) := Real.sqrt_sq (by nlinarith)

theorem sob_class : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  intro F _ _ κ _ N ψ hψ
  obtain ⟨μ, hμ, a, Cb, hB⟩ := GlobalTheory.T.measurable_periodic_arch_restriction F κ
  obtain ⟨Lw, K, hLw, hW⟩ := GlobalTheory.T.schwartz_polynomial_decay_words F κ ψ hψ N
  obtain ⟨L, D, Cs, hL, hS⟩ := GlobalTheory.T.sobolev_pointwise_bound_words F κ ψ hψ
  refine ⟨μ, hμ, D + N, a, max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0),
    fun Ψ hΨ m hm hper B hB0 hwords x => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hm)
  have hQ : 0 ≤ max Cs 0 * L.card * max Cb 0 := by positivity
  have hterm : ∀ l ∈ Lw, ‖wordH ψ l Ψ x‖ ≤ √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) := by
    intro l hl
    have hmem : wordH ψ l Ψ ∈ schA F κ := wordH_mem_sch ψ hψ l (fun w hw => ((hLw l hl).2 w hw).1) Ψ hΨ
    have h2 : ∀ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2 ≤
        ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
      intro l' hl'
      rw [← wordH_append]
      have hu : ∀ w ∈ l' ++ l, IsArchUnit w := by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact (hL l' hl').2 w hw
        · exact (hLw l hl).2 w hw
      have hmem' : wordH ψ (l' ++ l) Ψ ∈ schA F κ := wordH_mem_sch ψ hψ _ (fun w hw => (hu w hw).1) Ψ hΨ
      have hper' : PerM F m (wordH ψ (l' ++ l) Ψ) := wordH_perM ψ hper _ (fun w hw => (hu w hw).1)
      have hmeas : Measurable fun y : κ → mixedEmbedding.mixedSpace F => ‖wordH ψ (l' ++ l) Ψ (x + archInc F y)‖ₑ ^ 2 :=
        (continuous_slice hmem' x).measurable.enorm.pow_const 2
      have h5 := hB m hm (fun z => ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2) (fun z a' ha => by rw [hper' z a' ha]) x hmeas
      have hw := hwords (l' ++ l) (by rw [List.length_append]; have := (hL l' hl').1; have := (hLw l hl).1; omega) hu
      refine h5.trans ?_
      calc ENNReal.ofReal (Cb * (m : ℝ) ^ a) * ∫⁻ z, ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a) * ENNReal.ofReal B := by
            gcongr
            exact le_max_left _ _
        _ = ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := (ENNReal.ofReal_mul (by positivity)).symm
    have h3 : ‖wordH ψ l Ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
      refine (hS _ hmem x).trans ?_
      calc ENNReal.ofReal Cs * ∑ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2
          ≤ ENNReal.ofReal (max Cs 0) * ∑ _l' ∈ L, ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
            gcongr with l' hl'
            · exact le_max_left _ _
            · exact h2 l' hl'
        _ = ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    have h4 : ‖wordH ψ l Ψ x‖ ^ 2 ≤ max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B) := by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    exact sqrt_bound _ _ _ _ hQ hm1 hB0 (norm_nonneg _) (by simpa [mul_assoc] using h4)
  calc ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ K * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ := hW Ψ x
    _ ≤ max K 0 * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ max K 0 * ∑ _l ∈ Lw, √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (le_max_right _ _)
    _ = max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0) * (m : ℝ) ^ a * (1 + B) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end GlobalTheory.SobClass
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_uniform_bound_periodic : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  atlas_forward_decl GlobalTheory.SobClass.sob_class
end

section
open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

open GlobalTheory.RatPointSum in

theorem GlobalTheory.RatPointSum.norm_thetaSum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (M : ℕ) (B : ℝ) (Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ), 1 ≤ M →
      (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o) →
      (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ B) →
      ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ C * B * (M : ℝ) ^ N := by
  intro F _ _ κ _
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ one_pos
  set L := GlobalTheory.WeilM.denomLattice F κ 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  have hLn : ∀ z : L, 0 ≤ ((1 + ‖z‖) ^ r)⁻¹ := fun z => inv_nonneg.2 (by positivity)
  refine ⟨r, ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹, tsum_nonneg hLn, ?_⟩
  intro M B Ψ hM hsupp hdec
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (κ → F) := {ξ | ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o}
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F ((M : F) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding F ((M : F) * ξ i) ∈ mixedEmbedding.integerLattice F
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : F) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i)))
  let G : (κ → F) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace F, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  calc ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ ∑' ξ, G ξ := tsum_of_norm_bounded hGs.hasSum hbound
    _ = ∑' ξ : S, B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ := (tsum_subtype S _).symm
    _ = B * (M : ℝ) ^ r * ∑' ξ : S, (fun z : L => ((1 + ‖z‖) ^ r)⁻¹) (j ξ) := tsum_mul_left
    _ ≤ B * (M : ℝ) ^ r * ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hL hLn hj) (by positivity)
    _ = _ := by ring
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaDecay

theorem archAt_eq_ext (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (a : AF F) :
    archAt F w a = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := rfl

theorem evI_fst (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsReal}) :
    ((evI F a).1 v : ℂ) = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem evI_snd (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsComplex}) :
    (evI F a).2 v = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem norm_evI_sup : ∀ (F : Type) [Field F] [NumberField F] (a : AF F),
    (∀ w, ‖archAt F w a‖ ≤ ‖evI F a‖) ∧ ∀ B : ℝ, 0 ≤ B → (∀ w, ‖archAt F w a‖ ≤ B) → ‖evI F a‖ ≤ B := by
  intro F _ _ a
  refine ⟨fun w => ?_, fun B hB h => ?_⟩
  · rcases w.isReal_or_isComplex with hw | hw
    · have e := evI_fst F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).1 ⟨w, hw⟩‖ := by
        rw [← e, Complex.norm_real]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have e := evI_snd F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).2 ⟨w, hw⟩‖ := by rw [e]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  · rw [Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg hB).2 fun v => ?_, (pi_norm_le_iff_of_nonneg hB).2 fun v => ?_⟩
    · have := h v.1
      rw [← evI_fst F a v, Complex.norm_real] at this
      exact this
    · have := h v.1
      rw [← evI_snd F a v] at this
      exact this

end GlobalTheory.ThetaDecay
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embEquiv (w : InfinitePlace F) :
    letI : Algebra F ℂ := w.embedding.toAlgebra
    EmbOver E w ≃ (E →ₐ[F] ℂ) :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  { toFun := fun t => { t.1 with commutes' := fun x => RingHom.congr_fun t.2 x }
    invFun := fun s => ⟨s, RingHom.ext s.commutes⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

open Classical in
theorem embedding_trace (w : InfinitePlace F) (x : E) :
    w.embedding (Algebra.trace F E x) = ∑ τ : EmbOver E w, τ.1 x := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  have h := trace_eq_sum_embeddings (K := F) (L := E) ℂ (x := x)
  refine h.trans ?_
  exact (Fintype.sum_equiv (embEquiv w) _ _ fun _ => rfl).symm

theorem exists_repr_eq_trace (r : Fin (Module.finrank F E)) :
    ∃ c : E, ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x) := by
  classical
  refine ⟨(Module.finBasis F E).traceDual r, fun x => ?_⟩
  conv_rhs => rw [← (Module.finBasis F E).sum_repr x]
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
  simp

theorem archAt_algebraMap (w : InfinitePlace F) (x : F) :
    archAt F w (algebraMap F (AF F) x) = w.embedding x := by
  change InfinitePlace.Completion.extensionEmbedding w (evInf F w (algebraMap F (AF F) x)) = _
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

open Classical in
theorem archAt_repr (r : Fin (Module.finrank F E)) {c : E}
    (hc : ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x)) (w : InfinitePlace F) (y : AE F E) :
    archAt F w ((coB F E).repr y r) = ∑ τ : EmbOver E w, τ.1 c * piInf τ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul a x =>
    have h1 : (coB F E).repr (a ⊗ₜ[F] x) r = a * algebraMap F (AF F) ((Module.finBasis F E).repr x r) := by
      simp [coB, Algebra.TensorProduct.basis_repr_tmul]
    have h2 : ∀ τ : EmbOver E w, piInf τ (a ⊗ₜ[F] x) = archAt F w a * τ.1 x := fun τ => rfl
    rw [h1, map_mul, archAt_algebraMap, hc, embedding_trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [h2, map_mul]; ring

theorem coord_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : ℝ, 0 ≤ K ∧
    ∀ (y : AE F E) (B : ℝ), 0 ≤ B → (∀ (w : InfinitePlace F) (τ : EmbOver E w), ‖piInf τ y‖ ≤ B) →
    ∀ r w, ‖archAt F w ((coB F E).repr y r)‖ ≤ K * B := by
  classical
  intro F E _ _ _ _ _
  choose c hc using exists_repr_eq_trace (F := F) (E := E)
  let f : Fin (Module.finrank F E) × InfinitePlace F → ℝ := fun p => ∑ τ : EmbOver E p.2, ‖τ.1 (c p.1)‖
  have hf : ∀ p, 0 ≤ f p := fun p => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∑ p, f p, Finset.sum_nonneg fun p _ => hf p, fun y B hB h r w => ?_⟩
  rw [archAt_repr r (hc r) w y]
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := f) (fun p _ => hf p) (Finset.mem_univ (r, w))) hB))
  simp only [f]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h w τ) (norm_nonneg _)

end GlobalTheory.ThetaDecay.Coord

end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem arch_bound_functional (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n d : ℕ) (g : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AF F) (w : InfinitePlace F)
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) :
    ‖archAt F w (g x)‖ ≤ B * ∑ k, ∑ l, ∑ r, ‖archAt F w (g (Matrix.single k l (coB F E r)))‖ := by
  have hx' : x = ∑ k, ∑ l, ∑ r, (coB F E).repr (x k l) r • Matrix.single k l (coB F E r) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [← (coB F E).sum_repr (x k l)]
    simp only [Matrix.smul_single]
    exact map_sum (Matrix.singleAddMonoidHom k l) _ _
  rw [hx']
  simp only [map_sum, map_smul, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hx k l r) (norm_nonneg _)

theorem arch_bound_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) →
    ∀ w i, ‖archAt F w ((f x).1 i)‖ ≤ K * B ∧ ‖archAt F w ((f x).2 i)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let S : InfinitePlace F → κ → ℝ := fun w i =>
    (∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖) +
    ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖
  have hS : ∀ w i, 0 ≤ S w i := fun w i => by positivity
  refine ⟨∑ w, ∑ i, S w i, Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => hS w i, ?_⟩
  intro x B hB hx w i
  have hle : S w i ≤ ∑ w, ∑ i, S w i :=
    (Finset.single_le_sum (f := fun i => S w i) (fun i _ => hS w i) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun w => ∑ i, S w i)
        (fun w _ => Finset.sum_nonneg fun i _ => hS w i) (Finset.mem_univ w))
  have h1 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.fst _ _ _).comp f)) w x B hB (hx w)
  have h2 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.snd _ _ _).comp f)) w x B hB (hx w)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.fst_apply, LinearMap.snd_apply] at h1 h2
  have hA : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖ := by positivity
  have hC : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖ := by positivity
  constructor
  · refine h1.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_right hC).trans hle
  · refine h2.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_left hA).trans hle

end GlobalTheory.ThetaDecay
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem piInf_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = archAt F w a := by
  change infEmb τ (compInf F E w (a ⊗ₜ[F] 1)) = _
  unfold compInf
  simp [archAt]

theorem linMap_archBound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : (κ → AF F) × (κ → AF F) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (v : (κ → AF F) × (κ → AF F)) (B : ℝ), 0 ≤ B → (∀ w i, ‖archAt F w (v.1 i)‖ ≤ B ∧ ‖archAt F w (v.2 i)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (f v k l)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let e1 : κ → (κ → AF F) × (κ → AF F) := fun i => (Pi.single i 1, 0)
  let e2 : κ → (κ → AF F) × (κ → AF F) := fun i => (0, Pi.single i 1)
  let S : ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin d → ℝ := fun w τ k l =>
    ∑ i, (‖piInf τ (f (e1 i) k l)‖ + ‖piInf τ (f (e2 i) k l)‖)
  have hS : ∀ w τ k l, 0 ≤ S w τ k l := fun w τ k l =>
    Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => hS w τ k l, ?_⟩
  intro v B hB hv w τ k l
  have hvdec : v = ∑ i, (v.1 i • e1 i + v.2 i • e2 i) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [e1, e2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hfv : f v k l = ∑ i, (algebraMap (AF F) (AE F E) (v.1 i) * f (e1 i) k l +
      algebraMap (AF F) (AE F E) (v.2 i) * f (e2 i) k l) := by
    conv_lhs => rw [hvdec]
    simp only [map_sum, map_add, LinearMap.map_smul, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [Algebra.smul_def]
  have h1 : ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := by
    rw [hfv, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_add, map_mul, map_mul, piInf_algebraMap, piInf_algebraMap, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul_of_nonneg_right (hv w i).1 (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hv w i).2 (norm_nonneg _)
  have h2 : S w τ k l ≤ ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l)
      (fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l)
      (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, ∑ l, S w τ k l)
      (fun τ _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ l, S w τ k l)
      (fun k _ => Finset.sum_nonneg fun l _ => hS w τ k l) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun l => S w τ k l) (fun l _ => hS w τ k l) (Finset.mem_univ l)
  calc ‖piInf τ (f v k l)‖ ≤ B * S w τ k l := h1
    _ ≤ B * ∑ w, ∑ τ : EmbOver E w, ∑ k, ∑ l, S w τ k l := mul_le_mul_of_nonneg_left h2 hB
    _ = _ := mul_comm _ _

end GlobalTheory.ThetaDecay
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaFree

theorem schr_finset_sum {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) {ι : Type} (s : Finset ι) (φ : ι → (κ → R) → ℂ) :
    schr ψ w (∑ k ∈ s, φ k) = ∑ k ∈ s, schr ψ w (φ k) := by
  funext x
  simp only [schr, Finset.sum_apply, Finset.mul_sum]

theorem actAB_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E} (p : UA σ JX × UA σ JW) (a : AF F)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (a • u) = a • actAB (cA σ) p u := by
  simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]

theorem dH_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArch (M.co.e u) → dH B.ψ (M.co.e (actAB (cA σ) p u)) (om p Φ) = om p (dH B.ψ (M.co.e u) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ p u hu
  have hψ : IsStd B.ψ := hP.1
  have hS := IsUWeilPair.isUSplitting hP.2
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  have hAt : At (evI F) u := by
    intro a ha
    apply M.co.e.injective
    rw [map_smul, map_zero]
    exact Prod.ext (funext fun i => (hu i).1 a ha) (funext fun i => (hu i).2 a ha)
  obtain ⟨m, c, q, hq⟩ := Submodule.mem_span_set'.mp hΦ
  choose f g hg hfg using fun i => (q i).2
  set f' : Fin m → SInf F (Fin n × Fin d) := fun i => c i • f i with hf'
  have hΦe : Φ = ∑ i, pureA F (f' i) (g i) := by
    rw [← hq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfg i]
    funext x
    simp [f', pureA, mul_assoc]
  have hrho : ∀ (t : ℝ) (Ψ : (Fin n × Fin d → AF F) → ℂ),
      M.co.rho B.ψ (realAd F t • u) Ψ = schr B.ψ (realAd F t • M.co.e u) Ψ := by
    intro t Ψ
    rw [Darboux.rho, map_smul]

  have hdΦ : dH B.ψ (M.co.e u) Φ = ∑ i, pureA F (D u (f' i)) (g i) := by
    funext y
    have h : ∀ i, HasDerivAt (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y)
        (pureA F (D u (f' i)) (g i) y) 0 := by
      intro i
      have := (hD u hAt (f' i)).1 (g i) (hg i) (GlobalTheory.ExpAct.evalAt y) (GlobalTheory.ExpAct.evalAt_mem_adm F _ y)
      simpa only [GlobalTheory.ExpAct.evalAt, LinearMap.proj_apply, hrho] using this
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
    have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e u) Φ y) =
        fun t => ∑ i, schr B.ψ (realAd F t • M.co.e u) (pureA F (f' i) (g i)) y := by
      funext t
      rw [hΦe, schr_finset_sum, Finset.sum_apply]
    rw [dH, e, hs.deriv, Finset.sum_apply]
  funext x
  set l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.ExpAct.evalAt x ∘ₗ om p with hl
  have hladm : l ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm p _ (GlobalTheory.ExpAct.evalAt_mem_adm F _ x)
  have h : ∀ i, HasDerivAt (fun t : ℝ => l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))))
      (l (pureA F (D u (f' i)) (g i))) 0 := fun i => (hD u hAt (f' i)).1 (g i) (hg i) l hladm
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i
  have e : (fun t : ℝ => schr B.ψ (realAd F t • M.co.e (actAB (cA σ) p u)) (om p Φ) x) =
      fun t => ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) := by
    funext t
    have e1 : ∑ i, l (M.co.rho B.ψ (realAd F t • u) (pureA F (f' i) (g i))) = l (M.co.rho B.ψ (realAd F t • u) Φ) := by
      rw [← map_sum, hΦe, Darboux.rho, schr_finset_sum]
    rw [e1, hl, LinearMap.comp_apply, hS.impl p _ Φ hΦ, actAB_smul, Darboux.rho, map_smul]
    rfl
  rw [dH, e, hs.deriv, ← map_sum, hdΦ, hl, LinearMap.comp_apply]
  rfl

open scoped Classical in

theorem archUnit_act_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∃ C : ℝ, ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om _
  have evI_mul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 * b.1) = _
    exact map_mul _ _ _
  have evI_sub : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 - b.1) = _
    exact map_sub _ _ _
  have evI_one : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have evI_realAd : ∀ t : ℝ, evI F (realAd F t) = algebraMap ℝ _ t := fun t => by
    simp only [evI, realAd, LinearMap.inl_apply, RingEquiv.apply_symm_apply]
  obtain ⟨K5, hK5, h5⟩ := GlobalTheory.ThetaDecay.linMap_archBound F E n d (Fin n × Fin d) M.co.e.symm.toLinearMap
  obtain ⟨K3, hK3, h3⟩ := GlobalTheory.ThetaDecay.Coord.coord_bound F E
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.ThetaDecay.arch_bound_pair F E n d (Fin n × Fin d) M.co.e.toLinearMap
  refine ⟨K4 * (K3 * (n * d * K5)) + 1, fun p u hu => ?_⟩
  have hg : (1 : ℝ) ≤ ht p.1 := by
    have := one_le_heightGL F (p.1 : GL (Fin n) (AF F ⊗[F] E))
    exact_mod_cast this
  have hh : (1 : ℝ) ≤ ht p.2 := by
    have := one_le_heightGL F (p.2 : GL (Fin d) (AF F ⊗[F] E))
    exact_mod_cast this
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (ht p.1 : ℝ) * ht p.2 := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (K4 * (K3 * (n * d * K5)) + 1) * H := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    have : 0 < H := by rw [hH]; nlinarith
    positivity
  obtain ⟨x, hx⟩ : ∃ x, x = actAB (cA σ) p u := ⟨_, rfl⟩
  have s1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (u k l)‖ ≤ K5 * 1 := by
    have := h5 (M.co.e u) 1 zero_le_one (fun w i =>
      ⟨((GlobalTheory.ThetaDecay.norm_evI_sup F _).1 w).trans (hu.2 i).1, ((GlobalTheory.ThetaDecay.norm_evI_sup F _).1 w).trans (hu.2 i).2⟩)
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using this
  have s2 := GlobalTheory.WeilDirBound.norm_piInf_actAB_le_target F E σ n d X.J W.J p u (K5 * 1) (by positivity) s1
  rw [← hx, ← hH] at s2
  have s3 : ∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ K3 * (n * d * H * (K5 * 1)) :=
    fun w k l r => h3 (x k l) _ (by positivity) (fun w τ => s2 w τ k l) r w
  have s4 := h4 x _ (by positivity) s3
  have hbound : K4 * (K3 * (n * d * H * (K5 * 1))) ≤ c := by
    have e1 : K4 * (K3 * (n * d * H * (K5 * 1))) = K4 * (K3 * (n * d * K5)) * H := by ring
    rw [e1, hc]
    exact mul_le_mul_of_nonneg_right (by linarith) hH0
  have s5 : ∀ i, ‖evI F ((M.co.e x).1 i)‖ ≤ c ∧ ‖evI F ((M.co.e x).2 i)‖ ≤ c := fun i =>
    ⟨(GlobalTheory.ThetaDecay.norm_evI_sup F _).2 c hcpos.le (fun w => ((s4 w i).1).trans hbound),
     (GlobalTheory.ThetaDecay.norm_evI_sup F _).2 c hcpos.le (fun w => ((s4 w i).2).trans hbound)⟩
  have key : ∀ a : AF F, evI F a = 0 → a • M.co.e x = 0 := by
    intro a ha
    have h0 : a • M.co.e u = 0 := by
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · exact (hu.1 j).1 a ha
      · exact (hu.1 j).2 a ha
    have hu0 : a • u = 0 := by
      have := congrArg M.co.e.symm h0
      rwa [map_smul, LinearEquiv.symm_apply_apply, map_zero] at this
    rw [← map_smul, hx]
    have : a • actAB (cA σ) p u = actAB (cA σ) p (a • u) := by
      simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [this, hu0]
    simp [actAB]
  have harch : IsArch (M.co.e x) := fun i =>
    ⟨fun a ha => by simpa using congrArg (fun z => z.1 i) (key a ha),
     fun a ha => by simpa using congrArg (fun z => z.2 i) (key a ha)⟩
  have hone : ∀ z : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), IsArch z → realAd F 1 • z = z := by
    intro z hz
    have h1 : evI F (1 - realAd F 1) = 0 := by
      rw [evI_sub, evI_one, evI_realAd, map_one, sub_self]
    have : (1 - realAd F 1) • z = 0 :=
      Prod.ext (funext fun j => (hz j).1 _ h1) (funext fun j => (hz j).2 _ h1)
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  refine ⟨c, hcpos.le, by rw [hc, hH], realAd F c⁻¹ • M.co.e x, ⟨isArch_smul harch _, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).1 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).1 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).1 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).2 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).2 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).2 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · rw [smul_smul, realAd_mul, mul_inv_cancel₀ hcpos.ne', hone _ harch, hx]

theorem periodic_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ ∀ x a : Fin n × Fin d → AF F, (∀ i, evI F (a i) = 0 ∧ ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F) → om (g, h) Φ (x + (m : AF F) • a) = om (g, h) Φ x := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))
  refine ⟨m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((m₀ * N : ℕ) : ℝ) = m₀ * N := by push_cast; ring
    rw [this, mul_assoc (m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ := by
    clear hNle hC
    intro y hy
    set w' := M.co.e.symm (y, 0) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h2 h1
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  intro x a ha
  have hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a) := by
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · change fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0
      rw [map_mul]
      have h0 : fstA F (a i) = 0 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1
      rw [h0, mul_zero]
    · change ‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _
      rw [map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))
  have := congrFun (hfix _ hy) x
  simpa [schr] using this

theorem std_char_denom : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ D : ℕ, 0 < D ∧
    ∀ ξ : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) ξ * t) = 1) →
      ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _ ψ hψ
  obtain ⟨D, hD, h⟩ := GlobalTheory.exists_den_traceDual_ringOfIntegers (F := F)
  refine ⟨D, hD, fun ξ hξ => h ξ fun o => GlobalTheory.TraceIntStd.trace_int_of_isStd ψ hψ _ fun t ht0 ht1 => ?_⟩
  have e : algebraMap F (AF F) (ξ * o) * t = algebraMap F (AF F) ξ * (algebraMap F (AF F) o * t) := by
    rw [map_mul, mul_assoc]
  rw [e]
  refine hξ _ ?_ fun v => ?_
  · rw [show (algebraMap F (AF F) (o : F) * t).1 = (algebraMap F (AF F) (o : F)).1 * t.1 from rfl, ht0, mul_zero]
  · rw [map_mul, AlgHom.commutes, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ht1 v)
    refine Valued.toNormedField.norm_le_one_iff.2 ?_
    first
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact v.valuation_le_one o)
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact v.valuation_le_one o)
      | (exact (HeightOneSpectrum.coe_mem_adicCompletionIntegers v o))

theorem support_denom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (m : F) * ξ i = o := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hsp := hP.2.isUSplitting
  have hstd : IsStd B.ψ := hP.1
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨D, hD, hcond⟩ := std_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom M.co.e
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((D * m₀ * N : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)

  intro ξ hξ i
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (0, y) (om (g, h) Φ) = om (g, h) Φ := by
    clear hξ hcond hNle hC
    intro y hy
    set w' := M.co.e.symm (0, y) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h1 h2
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  obtain ⟨o, ho⟩ := hcond _ (fin_step B.ψ (m₀ * N) _ hfix ξ hξ i)
  exact ⟨o, by rw [← ho]; push_cast; ring⟩

section

variable {F : Type} [Field F] [NumberField F]

theorem evI_algebraMap_eq (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

open scoped Classical in
theorem sum_places_le : ∃ c : ℝ, ∀ ξ : F, ∑ w : InfinitePlace F, w ξ ≤ c * ‖evI F (algebraMap F (AF F) ξ)‖ := by
  refine ⟨Fintype.card (InfinitePlace F), fun ξ => ?_⟩
  rw [evI_algebraMap_eq]
  have h : ∀ w : InfinitePlace F, w ξ ≤ ‖mixedEmbedding F ξ‖ := by
    intro w
    rw [← mixedEmbedding.normAtPlace_apply w ξ]
    by_cases hw : w.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  calc ∑ w : InfinitePlace F, w ξ ≤ ∑ _w : InfinitePlace F, ‖mixedEmbedding F ξ‖ := Finset.sum_le_sum fun w _ => h w
    _ = _ := by simp

end

section

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordH_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.ThetaDecay.dH_mem_schA F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

end

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := by
  unfold ht
  exact heightGL_inv F g.1

theorem actAB_mul_inv {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (p : UA σ X.J × UA σ W.J)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ u) = u := by
  simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Matrix.transpose _), ← Matrix.transpose_mul]
  simp

end

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem word_transport {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} (hP : IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) {C : ℝ}
    (hC : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w)
    (p : UA σ X.J × UA σ W.J) :
    ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), (∀ w ∈ l, IsArchUnit w) →
      ∃ (c : ℝ) (l' : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))), 0 ≤ c ∧
        c ≤ (C * ((ht p.1 : ℝ) * ht p.2)) ^ l.length ∧ (∀ w ∈ l', IsArchUnit w) ∧ l'.length = l.length ∧
        wordH B.ψ l (om p Φ) = (c : ℂ) • om p (wordH B.ψ l' Φ) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, [], zero_le_one, by simp, by simp, rfl, by simp⟩
  | cons w l ih =>
    intro hl
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := ih (fun v hv => hl v (by simp [hv]))
    have hw : IsArchUnit w := hl w (by simp)
    obtain ⟨c', hc'0, hc'le, w', hw', he'⟩ := hC p⁻¹ (M.co.e.symm w) (by simpa using hw)
    have hF' : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) :=
      wordH_mem B.ψ hP.1 l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hT := dH_transport F E σ B n d X W M χX χW om hP _ hF' p (actAB (cA σ) p⁻¹ (M.co.e.symm w))
      (by rw [he']; exact isArch_smul hw'.1 _)
    rw [actAB_mul_inv, LinearEquiv.apply_symm_apply, he', dH_realAd_smul, map_smul] at hT
    refine ⟨c * c', w' :: l', mul_nonneg hc0 hc'0, ?_, ?_, by simp [hlen], ?_⟩
    · rw [List.length_cons, pow_succ]
      have : c' ≤ C * ((ht p.1 : ℝ) * ht p.2) := by simpa [ht_inv] using hc'le
      exact mul_le_mul hcle this hc'0 (hc0.trans hcle)
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hw'
      · exact hl' v hv
    · rw [wordH_cons, he, dH_smul, hT, wordH_cons, smul_smul, Complex.ofReal_mul]

end

section

theorem lintegral_sq_norm_le_of_smul {α : Type} {m : MeasurableSpace α} (μ : Measure α) (f g : α → ℂ) (c : ℝ) (hc0 : 0 ≤ c)
    (he : f = (c : ℂ) • g) (B₀ K : ℝ) (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B₀) (hcK : c ^ 2 ≤ K) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (K * max B₀ 0) := by
  have hcc : ‖(c : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc0, ENNReal.ofReal_pow hc0]
  subst he
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by rw [hcc]; exact ENNReal.ofReal_ne_top), hcc]
  calc ENNReal.ofReal (c ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ
      ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (max B₀ 0) :=
        by gcongr; exact hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (c ^ 2 * max B₀ 0) := (ENNReal.ofReal_mul (sq_nonneg c)).symm
    _ ≤ ENNReal.ofReal (K * max B₀ 0) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcK (le_max_right _ _))

theorem final_arith (P A S H m c₅ C₃ C₄ C₂ B₀ : ℝ) (N a k₄ ℓ : ℕ) (hP0 : 0 ≤ P) (hA0 : 0 ≤ A)
    (hA : A ≤ max c₅ 1 * (1 + S)) (hm0 : 0 ≤ m) (hm : m ≤ C₄ * H ^ k₄) (hH : 1 ≤ H)
    (key : P * (1 + S) ^ N ≤ C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0)) :
    P * A ^ N ≤ max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))) *
      H ^ (k₄ * a + 2 * ℓ) := by
  have hB₀' : (0 : ℝ) ≤ max B₀ 0 := le_max_right _ _
  have hC₂' : (1 : ℝ) ≤ max C₂ 1 := le_max_right _ _
  have hc₅' : (1 : ℝ) ≤ max c₅ 1 := le_max_right _ _
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hm' : m ≤ max C₄ 1 * H ^ k₄ :=
    hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))
  have hBw0 : 0 ≤ (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 := mul_nonneg (pow_nonneg (by positivity) _) hB₀'
  have h1B : 1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 ≤ (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ) := by
    have hH1 : 1 ≤ H ^ (2 * ℓ) := one_le_pow₀ hH
    rw [mul_pow]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ max C₂ 1 by linarith) (2 * ℓ)]
  calc P * A ^ N ≤ P * (max c₅ 1 * (1 + S)) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA N) hP0
    _ = max c₅ 1 ^ N * (P * (1 + S) ^ N) := by rw [mul_pow]; ring
    _ ≤ max c₅ 1 ^ N * (C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0)) :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (by linarith) _)
    _ ≤ max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 * H ^ k₄) ^ a * ((1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ))) := by
        gcongr
        · exact le_max_left _ _
    _ = _ := by
        rw [mul_pow, ← pow_mul, pow_add, mul_comm k₄ a]
        ring

theorem decay_at_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (ξ : Fin n × Fin d → F), ‖om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ N
  classical
  have hstd : IsStd B.ψ := hP.1
  have hU := hP.2.isUSplitting
  obtain ⟨μ, hμ, ℓ, a, C₃, h3⟩ := GlobalTheory.T.sobolev_uniform_bound_periodic F (Fin n × Fin d) N B.ψ hstd
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.ThetaSobolevBase.exists_l2_bound_heisenberg_word F (Fin n × Fin d) B.ψ hstd μ hμ Φ hΦ ℓ
  obtain ⟨C₂, h2⟩ := archUnit_act_bound F E σ B n d X W M χX χW om hP
  obtain ⟨C₄, k₄, h4⟩ := periodic_level F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨c₅, h5⟩ := sum_places_le (F := F)
  have hC₂ : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ max C₂ 1 * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧
        M.co.e (actAB (cA σ) p u) = realAd F c • w := fun p u hu => by
    obtain ⟨c, h0, hle, w, hw, he⟩ := h2 p u hu
    exact ⟨c, h0, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))), w, hw, he⟩
  refine ⟨max c₅ 1 ^ N * (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))), k₄ * a + 2 * ℓ,
    fun g h ξ => ?_⟩
  have hH : (1 : ℝ) ≤ (ht g : ℝ) * ht h :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)
  have hCH : (1 : ℝ) ≤ max C₂ 1 * ((ht g : ℝ) * ht h) := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hH
  have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := hU.pres (g, h) Φ hΦ
  obtain ⟨m, hm1, hmle, hper⟩ := h4 g h
  have hwords : ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), l.length ≤ ℓ →
      (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH B.ψ l (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤
        ENNReal.ofReal ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) * max B₀ 0) := by
    intro l hl hu
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := word_transport hP hΦ hC₂ (g, h) l hu
    have hF : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) := wordH_mem B.ψ hstd l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hun := hU.unit μ hμ (g, h) _ hF
    have hc2 : c ^ 2 ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := by
      calc c ^ 2 ≤ ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ l.length) ^ 2 := pow_le_pow_left₀ hc0 hcle 2
        _ = (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * l.length) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := pow_le_pow_right₀ hCH (by omega)
    exact lintegral_sq_norm_le_of_smul μ _ _ c hc0 he B₀ _ (hun.trans_le (hB₀ l' (by omega) hl')) hc2
  have key := h3 (om (g, h) Φ) hΨ m hm1 hper _ (mul_nonneg (pow_nonneg (by linarith) _) (le_max_right _ _)) hwords
    (fun i => algebraMap F (AF F) (ξ i))
  have hS0 : 0 ≤ ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA0 : 0 ≤ 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => apply_nonneg w _)
  have hA : 1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * (1 + ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖) := by
    have : ∑ i, ∑ w : InfinitePlace F, w (ξ i) ≤ max c₅ 1 * ∑ i, ‖evI F (algebraMap F (AF F) (ξ i))‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => (h5 (ξ i)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ max c₅ 1 := le_max_right _ _
    nlinarith
  exact final_arith _ _ _ _ _ _ _ _ _ _ N a k₄ ℓ (norm_nonneg _) hA0 hA (Nat.cast_nonneg m) hmle hH key

end

theorem theta_moderateGrowth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), (IsStd B.ψ ∧ M.IsWeil B.ψ χX χW om) → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨N, C₀, hC₀, hcount⟩ := GlobalTheory.RatPointSum.norm_thetaSum_le F (Fin n × Fin d)
  obtain ⟨C₂, k₂, hsupp⟩ := support_denom F E σ B n d X W M χX χW om hP Φ hΦ
  obtain ⟨C₃, k₃, hdec⟩ := decay_at_rational F E σ B n d X W M χX χW om hP Φ hΦ N
  refine ⟨C₀ * C₃ * C₂ ^ N, k₃ + k₂ * N, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hm⟩ := hsupp g h
  set x : ℝ := (ht g : ℝ) * ht h
  have hB : 0 ≤ C₃ * x ^ k₃ := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ => w.1.nonneg _)) _)) (hdec g h 0)
  have key := hcount m (C₃ * x ^ k₃) (om (g, h) Φ) hm1 (hm) (hdec g h)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  calc ‖theta om Φ g h‖ = ‖GlobalTheory.WeilM.thetaSum F (om (g, h) Φ)‖ := rfl
    _ ≤ C₀ * (C₃ * x ^ k₃) * (m : ℝ) ^ N := key
    _ ≤ C₀ * (C₃ * x ^ k₃) * (C₂ * x ^ k₂) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmle N) (mul_nonneg hC₀ hB)
    _ = C₀ * C₃ * C₂ ^ N * x ^ (k₃ + k₂ * N) := by rw [mul_pow, pow_add, pow_mul]; ring

end GlobalTheory.ThetaFree

end
end
