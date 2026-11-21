import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

abbrev KapI {D : D7} (X : HidaSetting D) : Type :=
  Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
    Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F

def betaI {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
    (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w)).re

open Classical in

def matI {D : D7} (X : HidaSetting D) : Matrix (KapI X) (KapI X) ℝ :=
  fun i j => betaI X (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

open Classical in

def DensMu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (tupCoord X) = ENNReal.ofReal (Real.sqrt |(matI X).det|) • volume

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW.FSD

open MeasureTheory Real Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped FourierTransform RealInnerProductSpace

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem selfDual_lin (A : V ≃L[ℝ] V) (hA : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) :
    SelfDual (ENNReal.ofReal (Real.sqrt |LinearMap.det (A : V →ₗ[ℝ] V)|) • (volume : Measure V))
      (fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) := by
  set d := LinearMap.det (A : V →ₗ[ℝ] V) with hd_def
  have hd : d ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  set c := Real.sqrt |d| with hc_def
  have hc0 : 0 < c := Real.sqrt_pos.2 (abs_pos.2 hd)
  have hcc : c * c = |d| := Real.mul_self_sqrt (abs_nonneg d)
  have hcr : (ENNReal.ofReal c).toReal = c := ENNReal.toReal_ofReal hc0.le
  have hc1 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
  let e : V ≃ᵐ V := A.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = A y := fun _ => rfl
  have hmap : (volume : Measure V).map e = ENNReal.ofReal |d⁻¹| • volume := by
    show (volume : Measure V).map (A : V →ₗ[ℝ] V) = _
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hdi : (ENNReal.ofReal |d⁻¹|).toReal = |d|⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  refine ⟨Measure.IsAddHaarMeasure.smul (μ := (volume : Measure V)) hc1 ENNReal.ofReal_ne_top, fun Φ hc hs hI z => ?_⟩
  have hT : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂(ENNReal.ofReal c • (volume : Measure V)) =
      (c : ℂ) * 𝓕⁻ Φ (A y) := by
    intro y
    rw [integral_smul_measure, hcr, fourierInv_eq, Complex.real_smul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Circle.smul_def, smul_eq_mul]; ring)
  simp only [hT] at hI ⊢

  have hI1 : Integrable (fun y => (c : ℂ) * 𝓕⁻ Φ (A y)) volume :=
    (integrable_smul_measure hc1 ENNReal.ofReal_ne_top).1 hI
  have hI2 : Integrable (fun y => 𝓕⁻ Φ (e y)) volume := by
    have := hI1.const_mul ((c : ℂ)⁻¹)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [he]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hc0.ne'), one_mul]
  have hI3 : Integrable (𝓕⁻ Φ) volume := by
    have h := (integrable_map_equiv e (𝓕⁻ Φ)).2 hI2
    rw [hmap] at h
    exact (integrable_smul_measure (by simp [hd]) ENNReal.ofReal_ne_top).1 h
  have hF : Integrable (𝓕 Φ) volume := by
    have h := hI3.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [fourierInv_eq_fourier_neg, neg_neg]
  have hΦ : Integrable Φ volume := hc.integrable_of_hasCompactSupport hs
  have hinv : 𝓕⁻ (𝓕⁻ Φ) z = Φ (-z) := by
    rw [fourierInv_eq_fourier_neg]
    exact congrFun (hc.fourier_fourierInv_eq hΦ hF) (-z)

  have hout : ∫ y, (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ) ∂(volume : Measure V) =
      (c : ℂ) * (|d|⁻¹ : ℝ) * 𝓕⁻ (𝓕⁻ Φ) z := by
    have e1 : (fun y => (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ)) =
        fun y => (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) := by
      funext y
      simp only [he, hA y z]
      ring
    have key : ∫ y, (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) ∂(volume : Measure V) =
        ∫ u, (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u) ∂((volume : Measure V).map e) :=
      (integral_map_equiv e (fun u => (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u))).symm
    rw [e1, key, hmap, integral_smul_measure, hdi, integral_const_mul, fourierInv_eq,
      Complex.real_smul]
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  rw [integral_smul_measure, hcr, hout, hinv, Complex.real_smul]
  have : (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hcc, ← Complex.ofReal_mul, mul_inv_cancel₀ (abs_pos.2 hd).ne',
      Complex.ofReal_one]
  calc (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ) * Φ (-z)) = ((c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ))) * Φ (-z) := by
        ring
    _ = Φ (-z) := by rw [this, one_mul]

end PI.AprimeInfW.FSD
end
end

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure V) (χ : V → V → ℂ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  haveI := h.1
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  have hm : μ.map e = μ.map em := rfl
  refine ⟨ea.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  rw [hm] at hI ⊢
  have hT : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map em) = ∫ x, Φ (e x) * χ x (e.symm y) ∂μ := by
    intro y
    rw [integral_map_equiv]
    simp [em]
  simp only [hT] at hI ⊢
  rw [integrable_map_equiv] at hI
  rw [integral_map_equiv]
  simp only [em, Function.comp_def, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply] at hI ⊢
  rw [h.2 (fun x => Φ (e x)) (hc.comp e.continuous) (hs.comp_homeomorph e) hI (e.symm z)]
  show Φ (e (-e.symm z)) = Φ (-z)
  rw [show e (-e.symm z) = -z from by
    have := ea.map_neg (e.symm z)
    change e (-e.symm z) = -e (e.symm z) at this
    rw [this, e.apply_symm_apply]]

section Beta

variable {D : D7} (X : HidaSetting D)

theorem tupCoord_symm_add (x y : EuclideanSpace ℝ (KapI X)) :
    (tupCoord X).symm (x + y) = (tupCoord X).symm x + (tupCoord X).symm y := by
  apply (tupCoord X).injective
  rw [tupCoord_add]
  simp

theorem betaI_add_left (x x' y : EuclideanSpace ℝ (KapI X)) : betaI X (x + x') y = betaI X x y + betaI X x' y := by
  simp only [betaI, tupCoord_symm_add, BR_add_leftP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y)) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y) w from rfl,
    map_add, Complex.add_re]

theorem betaI_add_right (x y y' : EuclideanSpace ℝ (KapI X)) : betaI X x (y + y') = betaI X x y + betaI X x y' := by
  simp only [betaI, tupCoord_symm_add, BR_add_rightP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y')) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y') w from rfl,
    map_add, Complex.add_re]

theorem continuous_betaI_left (y : EuclideanSpace ℝ (KapI X)) : Continuous fun x => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)))

theorem continuous_betaI_right (x : EuclideanSpace ℝ (KapI X)) : Continuous fun y => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous)))

theorem betaI_smul_left (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X (r • x) y = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun x => betaI X x y) fun a b => betaI_add_left X a b y)
    (continuous_betaI_left X y) r x

theorem betaI_smul_right (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X x (r • y) = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun y => betaI X x y) fun a b => betaI_add_right X x a b)
    (continuous_betaI_right X x) r y

def betaL : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (betaI X) (betaI_add_left X) (fun r x y => betaI_smul_left X r x y) (betaI_add_right X)
    (fun r x y => betaI_smul_right X r x y)

open Classical in
theorem betaI_expand (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ i, ∑ j, x i * matI X i j * y j := by
  have h : betaI X x y = betaL X x y := rfl
  rw [h]
  conv_lhs => rw [← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr x, ← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [betaL, LinearMap.mk₂_apply, matI]
  ring

end Beta

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x

open Classical in

def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)

open Classical in

def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

open Classical in
theorem densMu_of (hS : BetaSym) (hN : MatND) : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by rw [det_Alin]; exact isUnit_iff_ne_zero.2 (hN X)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, hS]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sigE (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : E ≃ₐ[F] E :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)

theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ t) = Algebra.trace R (R ⊗[F] E) t := by
  have h : sigR R σ t = Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (sigE σ hσ) t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigE]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h, Algebra.trace_eq_of_algEquiv]

theorem hR_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    hR R σ J y x = sigR R σ (hR R σ J x y) := by
  have h := gramR_memP R σ hσ J hJ ![x, y] 0 1
  simp only [gramR, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, sigR_invP R σ hσ]

end Gen

theorem BR_symm {D : D7} (X : HidaSetting D) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y x := by
  simp only [BR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hR_swap (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) (x a) (y a),
    trace_sigR (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X)]

theorem betaSym_holds : BetaSym := by
  intro D X x y
  simp only [betaI]
  rw [BR_symm]

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem no_kernel {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (χ : W → W → ℂ) (hμ : SelfDual μ χ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hT : ST.TestExP μ χ) (t : W) (ht0 : t ≠ 0)
    (ht : ∀ y, χ t y = 1) : False := by
  haveI := hμ.1
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := hT

  have htr : ∀ y, ∫ x, Φ (x - t) * χ x y ∂μ = ∫ x, Φ x * χ x y ∂μ := by
    intro y
    have := integral_sub_right_eq_self (μ := μ) (fun x => Φ x * χ (x + t) y) t
    simp only [sub_add_cancel] at this
    rw [this]
    congr 1; funext x
    rw [hadd, ht, mul_one]
  have hc' : Continuous fun x => Φ (x - t) := hc.comp (continuous_id.sub continuous_const)
  have hs' : HasCompactSupport fun x => Φ (x - t) := hs.comp_homeomorph (Homeomorph.subRight t)
  have hper : ∀ w, Φ (w - t) = Φ w := by
    intro w
    have h1 := hμ.2 (fun x => Φ (x - t)) hc' hs' (by simp only [htr]; exact hI) (-w)
    have h2 := hμ.2 Φ hc hs hI (-w)
    simp only [htr, neg_neg] at h1 h2
    rw [← h1, h2]
  have hpern : ∀ n : ℕ, ∀ w, Φ (w - n • t) = Φ w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [succ_nsmul, ← sub_sub, hper, ih]
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  apply hz
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖-z‖) / ‖t‖)
  rw [← hpern n (-z)]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have h1 : ‖(n : ℝ) • t‖ ≤ ‖-z - n • t‖ + ‖-z‖ := by
    have := norm_sub_le (-z) (-z - n • t)
    simp only [sub_sub_cancel] at this
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this ⊢
    linarith [norm_sub_rev (-z) (-z - (n : ℝ) • t)]
  rw [norm_smul, Real.norm_natCast] at h1
  have h2 : (R + ‖-z‖) < n * ‖t‖ := by rwa [div_lt_iff₀ htpos] at hn
  linarith

open Classical in

def MatNDH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (matI X).det ≠ 0

theorem matNDH_holds : MatNDH := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP hdet0
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  let t : EuclideanSpace ℝ (KapI X) := (EuclideanSpace.equiv (KapI X) ℝ).symm v
  have ht0 : t ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (EuclideanSpace.equiv (KapI X) ℝ) h
    simpa [t] using this
  have hAt : Alin X t = 0 := by
    simp [Alin, t, Matrix.toLin'_apply]
    exact hv
  have hβ : ∀ y, betaI X t y = 0 := by
    intro y
    rw [betaSym_holds, ← inner_Alin, hAt, inner_zero_right]
  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  haveI := hμ'.1
  have hadd : ∀ x x' y : EuclideanSpace ℝ (KapI X), (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) (x + x') y = (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x y * (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x' y := by
    intro x x' y
    simp only [tupCoord_symm_add, BR_add_leftP, psiInf_addP]
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) :=
    { addL := hadd
      addR := fun x y y' => by simp only [tupCoord_symm_add, BR_add_rightP, psiInf_addP]
      norm1 := fun x y => norm_psiInfP ψ hS _
      contL := fun y => hpc.comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)
      contR := fun x => hpc.comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous) }
  have hTest := ST.testEx_bichar (μinf.map (tupCoord X)) hB
  refine no_kernel (μinf.map (tupCoord X)) _ hμ' hadd hTest t ht0 fun y => ?_
  rw [psiInf_eq ψ hS]
  beta_reduce
  have : (∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
      (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm t) ((tupCoord X).symm y) w)).re) = 0 := hβ y
  simp only [this]
  simp

open Classical in
theorem densMu_holds : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by
    rw [det_Alin]; exact isUnit_iff_ne_zero.2 (matNDH_holds X u' ψ hT μinf νinf fibInf hP)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, betaSym_holds]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW.GenericDensity

open scoped RealInnerProductSpace FourierTransform
open MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V W ι : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] [Fintype ι] [DecidableEq ι]

private theorem exists_linearMap_inner_eq_and_det_eq_gram_det (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (b : OrthonormalBasis ι ℝ W) :
    ∃ A : W →ₗ[ℝ] W, (∀ x y, β x y = ⟪x, A y⟫) ∧
      LinearMap.det A = (Matrix.of fun i j => β (b i) (b j)).det := by
  have sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x
  have sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y
  let A : W →ₗ[ℝ] W :=
    { toFun := fun y => ∑ i, β (b i) y • b i
      map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ x y, β x y = ⟪x, A y⟫ := by
    intro x y
    have h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y := by
      conv_lhs => rw [← b.sum_repr' x]
      change (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _
      rw [map_sum]
      simp [sL]
    have h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫ := by
      simp [A, inner_sum, inner_smul_right]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, mul_comm]
  refine ⟨A, hA, ?_⟩
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, hA]
  simp [OrthonormalBasis.repr_apply_apply]

private theorem integral_fourier_map_eq_neg_of_integrable (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (Φ : W → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) (μ.map e))
    (z : W) :
    ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) * ((𝐞 (β y z) : Circle) : ℂ) ∂(μ.map e)
      = Φ (-z) := by
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => hme.integral_map g
  have hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ) := fun x y => by
    simpa using hχ (e x) (e y)
  set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef
  have hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y) := by
    intro y
    simp only [hFdef, hmap, Function.comp_apply, hχ']
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ := by
    simp only [hF]
    exact hme.integrable_map_iff.mp hint
  have key := hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)
  have hneg : e (-(e.symm z)) = -z := by
    have := map_neg (AddMonoidHom.mk' e he) (e.symm z)
    simpa using this
  simp only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key
  rw [hmap]
  simp only [hFdef, hmap]
  exact key

private theorem false_of_degenerate_of_fourier_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hcL : ∀ y, Continuous fun x => β x y)
    (k : W) (hk : k ≠ 0) (hk0 : ∀ y, β k y = 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) * ((𝐞 (β y z) : Circle) : ℂ) ∂ν = Φ (-z)) :
    False := by
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let bump : ContDiffBump (0 : W) := ⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩
  let ψ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp bump.continuous
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψs' : HasCompactSupport (fun x => ψ (x + k)) := hψs.comp_homeomorph (Homeomorph.addRight k)
  let Φ : W → ℂ := fun x => ψ x - ψ (x + k)
  have hΦc : Continuous Φ := hψc.sub (hψc.comp (continuous_add_right k))
  have hΦs : HasCompactSupport Φ := hψs.sub hψs'
  have hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0 := by
    intro y
    let g : W → ℂ := fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)
    have hgc : Continuous g := by
      have := hcL y
      fun_prop
    have hg : Integrable g ν := hgc.integrable_of_hasCompactSupport hψs.mul_right
    have heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k) := by
      funext x
      simp only [Φ, g, hL, hk0, add_zero]
      ring
    rw [heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have key := hP Φ hΦc hΦs hint 0
  simp only [hzero, zero_mul, integral_zero, neg_zero] at key
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; positivity)
  have h1 : bump k = 0 := by
    apply Function.notMem_support.mp
    rw [bump.support_eq]
    simp
    exact le_rfl
  simp [Φ, ψ, h0, h1] at key

private theorem measure_eq_sqrt_abs_det_smul_volume_of_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (A : W →ₗ[ℝ] W)
    (hdet : LinearMap.det A ≠ 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) * ((𝐞 ⟪A y, z⟫ : Circle) : ℂ) ∂ν = Φ (-z)) :
    ν = ENNReal.ofReal (Real.sqrt |LinearMap.det A|) • volume := by
  set s := ν.addHaarScalarFactor volume with hsdef
  have hs : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = (s : ENNReal) • volume := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul ν volume
  let bump : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)
  let Φ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hΦs : HasCompactSupport Φ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))
  let S : SchwartzMap W ℂ := hΦs.toSchwartzMap hΦd
  have hSΦ : (S : W → ℂ) = Φ := rfl
  let g : W → ℂ := 𝓕⁻ Φ
  have hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ) := by rw [SchwartzMap.fourierInv_coe, hSΦ]
  have hgi : Integrable g := by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable
  have hgg : ∫ v, g v = 1 := by
    have h1 : 𝓕⁻ g 0 = ∫ v, g v := by simp [Real.fourierInv_eq]
    have h2 : 𝓕⁻ g 0 = Φ 0 := by
      rw [Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]
    rw [← h1, h2]
    simp [Φ, h0]
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hAm : AEMeasurable A volume := hAc.measurable.aemeasurable
  have hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hgim : Integrable g ((volume : Measure W).map A) := by
    rw [hmapA]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  have hgA : Integrable (fun y => g (A y)) volume :=
    (integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim
  have hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y) := by
    intro y
    show _ = (s : ℝ) • 𝓕⁻ Φ (A y)
    rw [hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]
    congr 1
    congr 1
    funext x
    rw [Circle.smul_def, smul_eq_mul, mul_comm]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν := by
    simp only [hinner]
    rw [hν]
    exact (hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top
  have hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ) := by
    rw [← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]
  have key := hP Φ hΦd.continuous hΦs hint 0
  simp only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  rw [hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)] at key
  have hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1 := by
    have h2 : Φ (-0) = 1 := by simp [Φ, h0]
    rw [h2] at key
    have := congrArg Complex.re key
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this
    exact this
  have hdpos : 0 < |LinearMap.det A| := abs_pos.mpr hdet
  have hsq : (s : ℝ) ^ 2 = |LinearMap.det A| := by
    rw [abs_inv] at hreal
    field_simp at hreal
    nlinarith [hreal]
  rw [hν]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]

theorem dens_generic (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (hS : ∀ x y, β x y = β y x) (b : OrthonormalBasis ι ℝ W) :
    μ.map e = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j => β (b i) (b j)).det|) • volume := by
  obtain ⟨A, hA, hdet⟩ := exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b
  have hP := fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective
      e.isClosedEmbedding.tendsto_cocompact
  by_cases hd : (Matrix.of fun i j => β (b i) (b j)).det = 0
  · exfalso
    rw [← hdet] at hd
    obtain ⟨k, hkker, hk⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
    have hk0 : ∀ y, β k y = 0 := fun y => by
      rw [hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]
    exact false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP
  · rw [← hdet] at hd ⊢
    apply measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd
    intro Φ hc hs hi z
    have hβ' : ∀ y z, ⟪A y, z⟫ = β y z := fun y z => by rw [hS, hA, real_inner_comm]
    simp only [← hA, hβ'] at hi ⊢
    exact hP Φ hc hs hi z

end PI.AprimeInfW.GenericDensity
end
end

section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {D : D7} (X : HidaSetting D)

def matCoord : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem matCoord_add (x y : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : matCoord X (x + y) = matCoord X x + matCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

def scalI (t : ℝ) : Ainf X.B.I.F := (ainfReal (totReal_of X)).symm fun _ => t

theorem matCoord_scal (t : ℝ) (S : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
    matCoord X (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * S a b) =
      t • matCoord X S := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  have hf : ∀ f : Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → InfinitePlace X.B.I.F → ℝ,
      flat4 _ _ _ _ (t • f) = t • flat4 _ _ _ _ f := by
    intro f
    show (EuclideanSpace.equiv _ ℝ).symm _ = t • (EuclideanSpace.equiv _ ℝ).symm _
    rw [← map_smul]
    rfl
  rw [← hf]
  congr 1
  funext a i k v
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  have h1 : tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (scalI X t • S a i) =
      scalI X t • tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) :=
    map_smul (Module.Free.chooseBasis (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).equivFun _ _
  rw [h1]
  show complReal v ((totReal_of X) v) ((scalI X t) v * _) = t * _
  rw [show complReal v ((totReal_of X) v) ((scalI X t) v * tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) =
      complReal v ((totReal_of X) v) ((scalI X t) v) *
        complReal v ((totReal_of X) v) (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) from
    map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal ((totReal_of X) v)) _ _]
  congr 1
  show ainfReal (totReal_of X) (scalI X t) v = t
  simp [scalI]

theorem herm_scal (t : ℝ) (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Matrix.of (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) := by
  intro a b
  have hS := S.2 a b
  simp only [Matrix.of_apply, map_mul]
  rw [hS]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem matCoord_symm_add (c c' : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (c + c') = (matCoord X).symm c + (matCoord X).symm c' := by
  apply (matCoord X).injective; rw [matCoord_add]; simp

theorem matCoord_symm_zero : (matCoord X).symm 0 = 0 := by
  apply (matCoord X).injective
  have h := matCoord_add X 0 0
  simp only [add_zero] at h
  rw [Homeomorph.apply_symm_apply]
  exact (by simpa using h : matCoord X 0 = 0).symm

theorem matCoord_symm_smul (t : ℝ) (c : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (t • c) = fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (matCoord X).symm c a b := by
  apply (matCoord X).injective; rw [matCoord_scal]; simp

def Wh : Submodule ℝ (EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) where
  carrier := {c | Matrix.of ((matCoord X).symm c) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)}
  add_mem' := by
    intro c c' hc hc'
    show Matrix.of ((matCoord X).symm (c + c')) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_add, ← Matrix.of_add_of]
    exact add_mem hc hc'
  zero_mem' := by
    show Matrix.of ((matCoord X).symm 0) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_zero, Matrix.of_zero]
    exact zero_mem _
  smul_mem' := by
    intro t c hc
    show Matrix.of ((matCoord X).symm (t • c)) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_smul]
    exact herm_scal X t ⟨_, hc⟩

theorem hermCoord_mem (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) ∈ Wh X := by
  show Matrix.of ((matCoord X).symm (matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))))) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
  rw [Homeomorph.symm_apply_apply, Equiv.apply_symm_apply]; exact S.2

def hermCoord : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ≃ₜ Wh X where
  toFun S := ⟨matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))), hermCoord_mem X S⟩
  invFun w := ⟨Matrix.of ((matCoord X).symm w), w.2⟩
  left_inv S := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp
  continuous_toFun := ((matCoord X).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((matCoord X).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem hermCoord_add (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : hermCoord X (S + T) = hermCoord X S + hermCoord X T := by
  apply Subtype.ext
  exact matCoord_add X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) (Matrix.of.symm (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))

theorem hermCoord_symm_add (x y : Wh X) :
    (hermCoord X).symm (x + y) = (hermCoord X).symm x + (hermCoord X).symm y := by
  apply (hermCoord X).injective; rw [hermCoord_add]; simp

end Coord

section Pair

variable {D : D7} (X : HidaSetting D)

theorem pairHerm_addL (S S' T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ (S + S') T =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S' T := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

theorem pairHerm_addR (S T T' : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S (T + T') =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T' := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem pairHerm_symm (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T = pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ T S := by
  simp only [pairHerm]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem continuous_pairHerm_leftP (T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => algebraMap X.B.I.F (Ainf X.B.I.F) (1 / 2) *
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
      (∑ a, ∑ b, (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b * (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) b a)
  refine continuous_const.mul ((continuous_traceP X).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

def sumReI (a : Ainf X.B.I.F) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w (a w)).re

theorem sumReI_add (a b : Ainf X.B.I.F) : sumReI X (a + b) = sumReI X a + sumReI X b := by
  simp only [sumReI]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (a + b) w = a w + b w from rfl, map_add, Complex.add_re]

theorem continuous_sumReI : Continuous (sumReI X) :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

def betaH (x y : Wh X) : ℝ := sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ((hermCoord X).symm x) ((hermCoord X).symm y))

end Pair

def DensNu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    νinf.map (hermCoord X) = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j =>
      betaH X (stdOrthonormalBasis ℝ (Wh X) i) (stdOrthonormalBasis ℝ (Wh X) j)).det|) • volume

theorem densNu_holds : DensNu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  have hS := hP.2.2.1
  have hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) := hP.2.2.2.2.2.1
  have h1 : ∀ x y : Wh X, (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) ((hermCoord X).symm x) ((hermCoord X).symm y) = ((𝐞 (betaH X x y) : Circle) : ℂ) := by
    intro x y
    simp only [betaH, sumReI]
    rw [psiInf_eq ψ hS, Real.fourierChar_apply]
    push_cast
    ring_nf
  have h2 : ∀ x x' y : Wh X, betaH X (x + x') y = betaH X x y + betaH X x' y := by
    intro x x' y
    simp only [betaH, hermCoord_symm_add, pairHerm_addL, sumReI_add]
  have h3 : ∀ x y y' : Wh X, betaH X x (y + y') = betaH X x y + betaH X x y' := by
    intro x y y'
    simp only [betaH, hermCoord_symm_add, pairHerm_addR, sumReI_add]
  have h4 : ∀ y : Wh X, Continuous fun x => betaH X x y := fun y =>
    (continuous_sumReI X).comp ((continuous_pairHerm_leftP X _).comp (hermCoord X).symm.continuous)
  have h6 : ∀ x y : Wh X, betaH X x y = betaH X y x := by
    intro x y
    simp only [betaH]
    rw [pairHerm_symm]
  have h5 : ∀ x : Wh X, Continuous fun y => betaH X x y := by
    intro x
    have e : (fun y => betaH X x y) = fun y => betaH X y x := funext fun y => h6 x y
    rw [e]
    exact h4 x
  exact PI.AprimeInfW.GenericDensity.dens_generic νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) hν (hermCoord X) (hermCoord_add X) (betaH X) h1 h2 h3 h4 h5 h6
    (stdOrthonormalBasis ℝ (Wh X))

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def PsiC {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ (KapI X) :=
  tupCoord X (κ z.1 • rmulT X (a (eH.symm z.2)) (Y0 X u'))

def PolarChartContDiffAt {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) : Prop :=
  ContDiffAt ℝ 1 (PsiC X u' a κ eH) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT))

open Classical in

def PsiDet {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (a : HmI X → MfI X) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ) : Prop :=
  ∃ (Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃L[ℝ] EuclideanSpace ℝ (KapI X)) (Dv : ℝ),
    fderiv ℝ (PsiC X u' a κ eH) ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) =
      (Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) →L[ℝ] EuclideanSpace ℝ (KapI X)) ∧
    0 < Dv ∧
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ = ENNReal.ofReal Dv • volume ∧
    Real.sqrt |(matI X).det| / (Dv * cν) = tVal X u'

theorem tVal_pos {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : 0 < tVal X u' := by
  have ht : 0 < Tw u' := by
    unfold Tw
    exact_mod_cast (D.mem u').A.T_prime.pos
  exact pow_pos ht _

theorem loc_glue {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F) (z0 : E) (Φ : E ≃L[ℝ] F)
    (h1 : ContDiffAt ℝ 1 f z0) (hd : fderiv ℝ f z0 = (Φ : E →L[ℝ] F)) :
    ∃ U ∈ 𝓝 z0, (∀ z ∈ U, HasFDerivWithinAt (Φ.symm ∘ f) ((Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)) U z) ∧
      Set.InjOn (Φ.symm ∘ f) U ∧
      ContinuousAt (fun z => |((Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)).det|) z0 ∧
      (Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z0) = ContinuousLinearMap.id ℝ E := by
  have hs := h1.hasStrictFDerivAt (by norm_num)
  rw [hd] at hs
  have hev := h1.eventually (by simp)
  have hPc : (hs.toOpenPartialHomeomorph f : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hsrc : (hs.toOpenPartialHomeomorph f).source ∈ 𝓝 z0 :=
    (hs.toOpenPartialHomeomorph f).open_source.mem_nhds hs.mem_toOpenPartialHomeomorph_source
  refine ⟨(hs.toOpenPartialHomeomorph f).source ∩ {z | ContDiffAt ℝ 1 f z}, inter_mem hsrc hev, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((Φ.symm.hasFDerivAt).comp z
      (((show ContDiffAt ℝ 1 f z from hz.2).differentiableAt one_ne_zero).hasFDerivAt)).hasFDerivWithinAt
  · intro z hz z' hz' e
    have e' : f z = f z' := Φ.symm.injective e
    rw [← hPc] at e'
    exact (hs.toOpenPartialHomeomorph f).injOn hz.1 hz'.1 e'
  · have hfd := h1.continuousAt_fderiv (by norm_num)
    have hc2 : ContinuousAt (fun z => (Φ.symm : F →L[ℝ] E).comp (fderiv ℝ f z)) z0 :=
      continuousAt_const.clm_comp hfd
    exact continuous_abs.continuousAt.comp (ContinuousLinearMap.continuous_det.continuousAt.comp hc2)
  · rw [hd]
    exact Φ.coe_symm_comp_coe

open Classical in
theorem tupJac_of_pieces {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT
    (μinf : Measure (TupI X)) (νinf : Measure (HmI X)) fibInf (hP : PushHyp X u' ψ hT μinf νinf fibInf)
    (Ω : Set (HmI X)) (a : HmI X → MfI X) (hC : IsChart X u' hT Ω a) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) {η : Type} [Fintype η]
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ) (hν : νinf.map eH = ENNReal.ofReal cν • volume)
    (h1 : PolarChartContDiffAt X u' hT a κ eH) (h2 : PsiDet X u' hT a κ eH cν) : TupJac X u' hT μinf νinf a κ := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : BorelSpace (HmI X) := ⟨rfl⟩
  obtain ⟨Φ, Dv, hd, hDv, hvol, harith⟩ := h2
  set z0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
    ((0 : EuclideanSpace ℝ ι), eH (TI X u' hT)) with hz0
  set f := PsiC X u' a κ eH with hf
  have hdetM : (matI X).det ≠ 0 := matNDH_holds X u' ψ hT μinf νinf fibInf hP
  have hsq : 0 < Real.sqrt |(matI X).det| := Real.sqrt_pos.2 (abs_pos.2 hdetM)
  have hcH : 0 < cν := by
    by_contra hne
    have h0 : cν = 0 := by
      rcases (not_lt.1 hne).lt_or_eq with h | h
      · exfalso
        have hz : ENNReal.ofReal cν = 0 := ENNReal.ofReal_of_nonpos h.le
        have := tVal_pos X u'
        rw [← harith] at this
        have hneg : Real.sqrt |(matI X).det| / (Dv * cν) < 0 := div_neg_of_pos_of_neg hsq (mul_neg_of_pos_of_neg hDv h)
        linarith
      · exact h
    have := tVal_pos X u'
    rw [← harith, h0, mul_zero, div_zero] at this
    exact lt_irrefl _ this

  have hvs : (volume : Measure (EuclideanSpace ℝ (KapI X))).map Φ.symm =
      (ENNReal.ofReal Dv)⁻¹ • volume := by
    have e1 : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) =
        ((volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ).map Φ.symm := by
      rw [Measure.map_map Φ.symm.continuous.measurable Φ.continuous.measurable]
      have : (Φ.symm ∘ Φ : _ → _) = id := funext fun z => Φ.symm_apply_apply z
      rw [this, Measure.map_id]
    rw [hvol, Measure.map_smul] at e1
    have hD0 : ENNReal.ofReal Dv ≠ 0 := by simpa using hDv
    rw [e1, smul_smul, ENNReal.inv_mul_cancel hD0 ENNReal.ofReal_ne_top, one_smul]
  set eT : TupI X ≃ₜ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) :=
    (tupCoord X).trans Φ.symm.toHomeomorph with heT
  have hμ : μinf.map eT = ENNReal.ofReal (Real.sqrt |(matI X).det| / Dv) • volume := by
    have e : (eT : TupI X → _) = Φ.symm ∘ tupCoord X := rfl
    rw [e, ← Measure.map_map Φ.symm.continuous.measurable (tupCoord X).continuous.measurable,
      densMu_holds X u' ψ hT μinf νinf fibInf hP, Measure.map_smul, hvs, smul_smul,
      ENNReal.ofReal_div_of_pos hDv, div_eq_mul_inv]

  obtain ⟨U, hUn, hder, hinj, hcont, hbase⟩ := loc_glue f z0 Φ h1 hd
  have hPsi : PsiM X u' a κ eT eH = Φ.symm ∘ f := rfl
  obtain ⟨Ω₁, hΩ₁, hΩ₁n, hnear⟩ := nearFacts_of isOpen_units_tens X u' ψ hT μinf νinf fibInf hP Ω a hC
  refine ⟨η, inferInstance, eT, eH, Real.sqrt |(matI X).det| / Dv, cν,
    fun z => (Φ.symm : EuclideanSpace ℝ (KapI X) →L[ℝ] (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).comp (fderiv ℝ f z), U,
    div_pos hsq hDv, hcH, hμ, hν, hUn, ?_, ?_, hcont, ?_, ?_⟩
  · rw [hPsi]; exact hder
  · rw [hPsi]; exact hinj
  · filter_upwards [hΩ₁n] with T hT1
    exact ⟨(hnear T hT1).1, (hnear T hT1).2 _ (hC.2.2.2 T (hΩ₁ hT1))⟩
  · have hid : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    simp only []
    rw [hbase, hid, abs_one, mul_one, div_div]
    exact harith

def TupPieces : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
    ∃ (η : Type) (_ : Fintype η) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), νinf.map eH = ENNReal.ofReal cν • volume ∧
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PolarChartContDiffAt X u' hT a (kap0 X hb c L) eH ∧ PsiDet X u' hT a (kap0 X hb c L) eH cν

theorem tupStd_of_pieces (h : TupPieces) : TupStd := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC, η, hη, eH, cν, hν, hJ⟩ := h X u' ψ hT μinf νinf fibInf hP
  refine ⟨Ω, a, hC, fun hb c S ι _ L hc hL => ?_⟩
  obtain ⟨h1, h2⟩ := hJ hb c S L hc hL
  exact tupJac_of_pieces X u' ψ hT μinf νinf fibInf hP Ω a hC _ eH cν hν h1 h2

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem euc_coords {V W : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure V) (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (c : ℝ)
    (h : μ.map e = ENNReal.ofReal c • volume) :
    ∃ eH : V ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ W)), (∀ x y, eH (x + y) = eH x + eH y) ∧
      μ.map eH = ENNReal.ofReal c • volume := by
  set R := (stdOrthonormalBasis ℝ W).repr with hR
  refine ⟨e.trans R.toHomeomorph, fun x y => ?_, ?_⟩
  · show R (e (x + y)) = R (e x) + R (e y)
    rw [he, map_add]
  · have e1 : ((e.trans R.toHomeomorph : V ≃ₜ _) : V → _) = R ∘ e := rfl
    rw [e1, ← Measure.map_map R.continuous.measurable e.continuous.measurable, h, Measure.map_smul,
      R.measurePreserving.map_eq]

def HermEuc : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (η : Type) (_ : Fintype η) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ),
      (∀ S T, eH (S + T) = eH S + eH T) ∧ νinf.map eH = ENNReal.ofReal cν • volume

theorem hermEuc : HermEuc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  obtain ⟨eH, hadd, hmap⟩ := euc_coords νinf (hermCoord X) (hermCoord_add X) _ (densNu_holds X u' ψ hT μinf νinf fibInf hP)
  exact ⟨_, inferInstance, eH, _, hadd, hmap⟩

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open Topology Filter

theorem exists_local_solution_contDiffAt {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      (∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y) ∧
      ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (e (B x0 x0 + L x0)) ∧
      HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (e (B x0 x0 + L x0)) := by
  classical
  have hes : ∀ u w, e.symm (u + w) = e.symm u + e.symm w := by
    intro u w
    apply e.injective
    rw [he]
    simp
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun u w => e (B (e.symm u) (e.symm w))
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun u => e (L (e.symm u))
  have hb1 : ∀ u u' w, b (u + u') w = b u w + b u' w := by
    intro u u' w
    simp only [b, hes, hB1, he]
  have hb2 : ∀ u w w', b u (w + w') = b u w + b u w' := by
    intro u w w'
    simp only [b, hes, hB2, he]
  have hl1 : ∀ u u', l (u + u') = l u + l u' := by
    intro u u'
    simp only [l, hes, hL, he]
  have hbc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2) :=
    e.continuous.comp (hBc.comp ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)))
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  have hbs1 : ∀ (c : ℝ) u w, b (c • u) w = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun u => b u w) (fun u u' => hb1 u u' w))
      (hbc.comp (continuous_id.prodMk continuous_const)) c u
  have hbs2 : ∀ (c : ℝ) u w, b u (c • w) = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun w => b u w) (fun w w' => hb2 u w w'))
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let b₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hbs1 hb2 hbs2
  let bL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ b₂)
  let lL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  have hbL : ∀ u w, bL u w = b u w := fun u w => rfl
  have hlL : ∀ u, lL u = l u := fun u => rfl
  let Ft : (Fin N → ℝ) → (Fin N → ℝ) := fun u => bL u u + lL u
  have hFt : ∀ u, Ft u = e (B (e.symm u) (e.symm u) + L (e.symm u)) := by
    intro u
    simp only [Ft, hbL, hlL, b, l, he]
  set u0 := e x0 with hu0
  have hy0 : Ft u0 = e (B x0 x0 + L x0) := by rw [hFt, hu0, e.symm_apply_apply]
  have hTwo : ∀ w, bL u0 w + bL w u0 + lL w = (2 : ℝ) • w := by
    intro w
    have h := congrArg e (hD (e.symm w))
    rw [he, he, he, e.apply_symm_apply] at h
    rw [hbL, hbL, hlL, two_smul]
    simpa [b, l, hu0] using h
  let f₁ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  let f₂ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  have h12 : Function.LeftInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  have h21 : Function.RightInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  let fe : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h12 h21
  have hFs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 := by
    have h0 := (bL.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id u0)
      (hasStrictFDerivAt_id u0)).add lL.hasStrictFDerivAt
    refine h0.congr_fderiv ?_
    ext1 w
    show bL u0 w + bL w u0 + lL w = (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) w
    rw [hTwo]
    rfl
  have hcd : ContDiffAt ℝ 1 Ft u0 :=
    ((bL.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).add
      lL.contDiff).contDiffAt
  have hs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 :=
    hcd.hasStrictFDerivAt' hFs.hasFDerivAt one_ne_zero
  let G := hcd.localInverse hFs.hasFDerivAt one_ne_zero
  have hGc : ContinuousAt G (Ft u0) := hs.localInverse_continuousAt
  have hGa : G (Ft u0) = u0 := hs.localInverse_apply_image
  have hGr : ∀ᶠ w in 𝓝 (Ft u0), Ft (G w) = w := hs.eventually_right_inverse
  have hGd : ContDiffAt ℝ 1 G (Ft u0) := hcd.to_localInverse hFs.hasFDerivAt one_ne_zero
  have hGf : HasFDerivAt G ((fe.symm : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (Ft u0) :=
    hs.to_localInverse.hasFDerivAt
  rw [hy0] at hGc hGa hGr hGd hGf
  refine ⟨fun y => e.symm (G (e y)), ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (hGc.comp e.continuous.continuousAt)
  · simp only [hGa, hu0, e.symm_apply_apply]
  · have ht : ∀ᶠ y in 𝓝 (B x0 x0 + L x0), Ft (G (e y)) = e y :=
      (e.continuous.tendsto (B x0 x0 + L x0)).eventually hGr
    filter_upwards [ht] with y hy
    rw [hFt] at hy
    exact e.injective (by rw [he]; simpa [he] using hy)
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    exact hGd
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    convert hGf using 1
    ext1 w
    rfl

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

theorem square_chart_c1_local {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → E) (hT : ∀ i j, σ (gramE σ J Y j i) = gramE σ J Y i j) (hdet : (gramE σ J Y).det ≠ 0)
    {N : ℕ} (e : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ (Ω : Set (HermR (Ainf F) σ m)) (a : HermR (Ainf F) σ m → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)),
      Ω ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧ a (hermOf (Ainf F) σ (gramE σ J Y) hT) = 1 ∧
      ContinuousAt a (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧
      (∀ T ∈ Ω, gramR (Ainf F) σ J (fun b i => ∑ c, a T c b * ratTup (Ainf F) Y c i) = (T : Matrix _ _ _)) ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HermR (Ainf F) σ m ≃ₜ EuclideanSpace ℝ η)
        (eM : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v =
          (1 / 2 : ℝ) • eM ((gramE σ J Y)⁻¹.map (inclR (Ainf F)) *
            ((eH.symm v : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))) := by
  classical
  set G := gramE σ J Y with hG
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set Tm : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G.map (inclR (Ainf F)) with hTm
  set Ti : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G⁻¹.map (inclR (Ainf F)) with hTi
  have hTTi : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTiT : Ti * Tm = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    Formalism.UG.cT (sigR (Ainf F) σ) with hc
  have hsig := sq_sig_inv (Ainf F) σ hσ
  have hcc : ∀ P, c (c P) = P := by intro P; ext i j; simp [hc, Formalism.UG.cT, hsig]
  have hcadd : ∀ P Q, c (P + Q) = c P + c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcsub : ∀ P Q, c (P - Q) = c P - c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcmul : ∀ P Q, c (P * Q) = c Q * c P := fun P Q => Formalism.UG.cT_mul _ P Q
  have hc1 : c 1 = 1 := Formalism.UG.cT_one _
  have hcT : c Tm = Tm := by
    ext i j
    simp only [hc, Formalism.UG.cT, hTm, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hT i j]
    simp [sigR, inclR]
  have hcTi : c Ti * Tm = 1 := by
    calc c Ti * Tm = c Ti * c Tm := by rw [hcT]
      _ = c (Tm * Ti) := (hcmul Tm Ti).symm
      _ = 1 := by rw [hTTi, hc1]
  have hcont_c : Continuous c := by
    show Continuous fun P : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) => (P.map (sigR (Ainf F) σ))ᵀ
    exact (continuous_id.matrix_map (continuous_sigRP (Ainf F) σ)).matrix_transpose
  set Bq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) →
      Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := fun h k => c (Ti * h) * Tm * (Ti * k) with hBq
  set Lq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    fun h => h - c h with hLq
  have hD : ∀ u, Bq Tm u + Bq u Tm + Lq u = u + u := by
    intro u
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Tm Ti u, hTTi, Matrix.one_mul, hcmul Ti u,
      Matrix.mul_assoc (c u) (c Ti) Tm, hcTi, Matrix.mul_one]
    abel
  obtain ⟨g, hgc, hg0, hgev, hgcd, hgd⟩ := exists_local_solution_contDiffAt e he Bq
    (by intro x x' y; simp only [hBq, Matrix.mul_add, hcadd, Matrix.add_mul])
    (by intro x y y'; simp only [hBq, Matrix.mul_add])
    (((hcont_c.comp (continuous_const.matrix_mul continuous_fst)).matrix_mul continuous_const).matrix_mul
      (continuous_const.matrix_mul continuous_snd))
    Lq (by intro x y; simp only [hLq, hcadd]; abel) (continuous_id.sub hcont_c) Tm hD
  have hy0 : Bq Tm Tm + Lq Tm = Tm := by
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, hcT, sub_self, add_zero]
  rw [hy0] at hgc hg0 hgev hgcd hgd
  refine ⟨Subtype.val ⁻¹' {y | Bq (g y) (g y) + Lq (g y) = y}, fun T => Ti * g T.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hgev
  · show Ti * g Tm = 1
    rw [hg0, hTiT]
  · exact (continuous_const.matrix_mul continuous_id).continuousAt.comp
      (ContinuousAt.comp_of_eq hgc continuous_subtype_val.continuousAt rfl)
  · intro T hT'
    have hT'' : Bq (g T.val) (g T.val) + Lq (g T.val) = T.val := hT'
    show gramR (Ainf F) σ J (fun b i => ∑ c, (Ti * g T.val) c b * ratTup (Ainf F) Y c i) = T.val
    rw [sq_gramR_rmul (Ainf F) σ J (Ti * g T.val) (ratTup (Ainf F) Y), gramR_ratTup]
    set h := g T.val
    have hP : c (Bq h h) = Bq h h := by
      simp only [hBq]
      rw [hcmul (c (Ti * h) * Tm) (Ti * h), hcmul (c (Ti * h)) Tm, hcc, hcT, Matrix.mul_assoc]
    have hTh : c T.val = T.val := by
      ext i j
      exact T.2 i j
    have hLL : c (Lq h) = -(Lq h) := by
      simp only [hLq]
      rw [hcsub, hcc]
      abel
    have h2 : Lq h + Lq h = 0 := by
      have e1 := congrArg c hT''
      rw [hcadd, hP, hLL, hTh] at e1
      have e2 := add_left_cancel (hT''.trans e1.symm)
      exact eq_neg_iff_add_eq_zero.mp e2
    have h0 : Lq h = 0 := by
      calc Lq h = ((1 / 2 : F) * 2) • Lq h := by norm_num
        _ = (1 / 2 : F) • (Lq h + Lq h) := by rw [mul_smul, two_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [h0, add_zero] at hT''
    exact hT''
  · intro η μ' _ _ eH eM heH heM
    have hHs : ∀ x y, eH.symm (x + y) = eH.symm x + eH.symm y := by
      intro x y; apply eH.injective; rw [heH]; simp
    have hes : ∀ x y, e.symm (x + y) = e.symm x + e.symm y := by
      intro x y; apply e.injective; rw [he]; simp
    let L₁ : EuclideanSpace ℝ η →L[ℝ] (Fin N → ℝ) :=
      (AddMonoidHom.mk' (fun z => e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))
        (by intro x y; simp only [hHs, AddSubgroup.coe_add, he])).toRealLinearMap
        (e.continuous.comp (continuous_subtype_val.comp eH.symm.continuous))
    let L₂ : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ μ' :=
      (AddMonoidHom.mk' (fun y => eM (Ti * e.symm y)) (by intro x y; simp only [hes, Matrix.mul_add, heM])).toRealLinearMap
        (eM.continuous.comp ((continuous_const.matrix_mul continuous_id).comp e.symm.continuous))
    have hL₁ : ∀ z, L₁ z = e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)) := fun z => rfl
    have hL₂ : ∀ y, L₂ y = eM (Ti * e.symm y) := fun y => rfl
    have hfun : (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))) =
        fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z)) := by
      funext z
      rw [hL₁, hL₂]
      simp only [Homeomorph.symm_apply_apply]
    have hpt : L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) = e Tm := by
      rw [hL₁, Homeomorph.symm_apply_apply]; rfl
    have hgcd' : ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgcd
    have hgd' : HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgd
    have hD := L₂.hasFDerivAt.comp (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) (hgd'.comp _ L₁.hasFDerivAt)
    refine ⟨?_, ?_⟩
    · show ContDiffAt ℝ 1 (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))
      rw [hfun]
      exact L₂.contDiff.contDiffAt.comp _ (hgcd'.comp _ L₁.contDiff.contDiffAt)
    · intro v
      show fderiv ℝ (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v = _
      have hD' : HasFDerivAt (fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z))) _
          (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) := hD
      rw [hfun, hD'.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul]
      rw [hL₂, hL₁, Homeomorph.symm_apply_apply]

def TinvI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : MfI X :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))⁻¹.map (inclR (Ainf X.B.I.F))

def SquareChartC1 : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
        (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
          (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

theorem square_chart_c1 : SquareChartC1 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨Ω, a, h1', h2', h3', h4', h5'⟩ :=
    square_chart_c1_local X.B.I.cm.sig hσ X.B.I.J (tupH (frameOf X u')) hT hdet eM hM
  exact ⟨Ω, a, ⟨h1', h2', h3', fun T hT' => h4' T hT'⟩, fun eH eM' heH heM => h5' eH eM' heH heM⟩

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ChartD {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a : HmI X → MfI X) : Prop :=
  ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
    (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
    (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
    ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
    ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
      (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

def PolarMapContDiffAtBase : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → ChartD X u' hT a →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η), (∀ S T, eH (S + T) = eH S + eH T) →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PolarChartContDiffAt X u' hT a (kap0 X hb c L) eH

def TupDet : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → ChartD X u' hT a →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), (∀ S T, eH (S + T) = eH S + eH T) →
    νinf.map eH = ENNReal.ofReal cν • volume →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → PsiDet X u' hT a (kap0 X hb c L) eH cν

theorem tupPieces_of (h1 : PolarMapContDiffAtBase) (h2 : TupDet) : TupPieces := by
  intro D X u' ψ hT μinf νinf fibInf hP
  obtain ⟨Ω, a, hC, hD⟩ := square_chart_c1 X u' ψ hT μinf νinf fibInf hP
  obtain ⟨η, hη, eH, cν, hadd, hν⟩ := hermEuc X u' ψ hT μinf νinf fibInf hP
  refine ⟨Ω, a, hC, η, hη, eH, cν, hν, fun hb c S ι _ L hc hL => ⟨?_, ?_⟩⟩
  · exact h1 X u' ψ hT μinf νinf fibInf hP Ω a hC hD eH hadd hb c S L hc hL
  · exact h2 X u' ψ hT μinf νinf fibInf hP Ω a hC hD eH cν hadd hν hb c S L hc hL

theorem tupStd_of_two (h1 : PolarMapContDiffAtBase) (h2 : TupDet) : TupStd := tupStd_of_pieces (tupPieces_of h1 h2)

end PI.AprimeInfW
end
end
