import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumIsFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFourierTransform

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero hz i, add_zero]
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).unit μA hμA (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) hS
  have hAct : om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_residue_character_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  atlas_forward_decl GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineContPairLeft

theorem continuous_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ hγ T hAct f x
  classical
  let κ := Fin n × Fin d
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hW.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => (γ (Multiplicative.ofAdd t), (1 : UA σ W.J))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp ((hγ.1.comp continuous_ofAdd).prodMk continuous_const)

end GlobalTheory.ArchLineContPairLeft
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  atlas_forward_decl GlobalTheory.ArchLineContPairLeft.continuous_apply
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.lmulL (k := d) (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ X.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t))) :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let Ru : Matrix (Fin n) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
      { toFun := fun x => x * u, map_add' := fun x y => Matrix.add_mul x y u,
        map_smul' := fun c x => Matrix.smul_mul c x u }
    let K := M.co.e.toLinearMap ∘ₗ Ru
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show mat (γ (Multiplicative.ofAdd (s + t))) * x =
      mat (γ (Multiplicative.ofAdd s)) * (mat (γ (Multiplicative.ofAdd t)) * x)
    rw [ofAdd_add, map_mul, hmat, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show mat (γ (Multiplicative.ofAdd 0)) * x = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.one_mul]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u = L t u := by
      show (mat (γ (Multiplicative.ofAdd t))) * u * ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1ᵀ =
        mat (γ (Multiplicative.ofAdd t)) * u
      rw [show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weil_line_intertwines_heisenberg_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  atlas_forward_decl GlobalTheory.ArchLineAct.intertwine_pair_left
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

theorem weil_heisDeriv_intertw_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J)
    (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTg : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD
  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (g, 1) (pureA F f' g') = pureA F (Tg f') g' := by
    intro f' g' hg
    have hr : Rest (evI F) (⇑f') (fun x => g' (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g', hg, rfl⟩⟩
      show g' _ = g' _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTg f' _ hr
  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := mat g * u with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (g, 1) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Tg f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Tg f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (g, 1) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.mul_smul]
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Tg f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (g : UA σ X.J) (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) → ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1 (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  atlas_forward_decl GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open GlobalTheory.HeisOrbit GlobalTheory.HeisOrbitSmooth

noncomputable section

namespace GlobalTheory.HeisOrbitSmoothLeft

open scoped ContDiff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

theorem at_mul_left {x : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evI F) x) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    At (evI F) (A * x) := by
  intro a ha
  rw [← Matrix.mul_smul, hx a ha, Matrix.mul_zero]

theorem continuous_mat_line_left (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous fun t : ℝ => mat (γ (Multiplicative.ofAdd t)) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))

theorem mat_mul_left (g h : UA σ X.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one_left : mat (1 : UA σ X.J) = 1 := rfl

def opLl (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) : (Vs (Fin n × Fin d)) →ₗ[ℝ] Vs (Fin n × Fin d) where
  toFun w := GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w)
  map_add' w w' := by rw [lift_add, Matrix.mul_add, archCo_add]
  map_smul' c w := by rw [lift_smul, Matrix.mul_smul, archCo_smul]; rfl

theorem opLl_apply (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) (w) :
    opLl M g w = GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w) := rfl

theorem opLl_archCo (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) {x : Matrix (Fin n) (Fin d) (AE F E)}
    (hx : At (evI F) x) : opLl M g (GlobalTheory.HeisOrbit.archCo M.co x) = GlobalTheory.HeisOrbit.archCo M.co (g * x) := by
  rw [opLl_apply, lift_archCo M.co hx]

def opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) :
    (Vs (Fin n × Fin d)) →L[ℝ] Vs (Fin n × Fin d) :=
  LinearMap.toContinuousLinearMap (opLl M (mat (γ (Multiplicative.ofAdd t))))

theorem opRl_apply (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) (w) :
    opRl M γ t w = opLl M (mat (γ (Multiplicative.ofAdd t))) w := rfl

theorem opRl_zero (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) : opRl M γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [opRl_apply, opLl_apply, ofAdd_zero, map_one, mat_one_left, Matrix.one_mul, archCo_lift]
  rfl

theorem opRl_add (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (s t : ℝ) :
    opRl M γ (s + t) = opRl M γ s * opRl M γ t := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.mul_apply, opRl_apply, opRl_apply, opRl_apply,
    opLl_apply M (mat (γ (Multiplicative.ofAdd t))) w,
    opLl_archCo M _ (at_mul_left (at_lift M.co w) _),
    opLl_apply, ofAdd_add, map_mul, mat_mul_left, Matrix.mul_assoc]

theorem continuous_opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous (opRl M γ) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  refine continuous_clm_apply.2 fun w => ?_
  simp only [opRl_apply, opLl_apply]
  exact (continuous_archCo M).comp ((continuous_mat_line_left γ hγ).matrix_mul continuous_const)

theorem archCo_orbit_smooth_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ u hu
  haveI : CompleteSpace ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    FiniteDimensional.complete ℝ _
  haveI : FiniteDimensional ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    ContinuousLinearMap.finiteDimensional
  have hcomp : CompleteSpace (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    FiniteDimensional.complete ℝ _
  have hs : ContDiff ℝ ∞ (opRl M γ) :=
    @GlobalTheory.contDiff_of_continuous_oneParameter _ _ _ hcomp (opRl M γ) (continuous_opRl M γ hγ.1) (opRl_zero M γ)
      (opRl_add M γ)
  have hf : (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) =
      fun t => opRl M γ t (GlobalTheory.HeisOrbit.archCo M.co u) := by
    funext t
    rw [opRl_apply, opLl_archCo M _ hu]
  rw [hf]
  refine ⟨hs.clm_apply contDiff_const, lift M.co (deriv (opRl M γ) 0 (GlobalTheory.HeisOrbit.archCo M.co u)), at_lift _ _, ?_⟩
  rw [archCo_lift]
  have hd : HasDerivAt (opRl M γ) (deriv (opRl M γ) 0) 0 :=
    ((hs.differentiable (by simp)) 0).hasDerivAt
  simpa using hd.clm_apply (hasDerivAt_const (0 : ℝ) (GlobalTheory.HeisOrbit.archCo M.co u))

end GlobalTheory.HeisOrbitSmoothLeft

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  atlas_forward_decl GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLieFockX

theorem lineGroupX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) =
        (γ (Multiplicative.ofAdd s), (1 : UA σ W.J)) * (γ (Multiplicative.ofAdd t), 1) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

theorem vacX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := lineGroupX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := GlobalTheory.T.weil_model_residue_character_pow F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := GlobalTheory.T.archimedean_weil_line_intertwines_heisenberg_left F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_isFockVacuum F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem heisX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co v).1 (GlobalTheory.HeisOrbit.archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth (W := W) M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).1
        (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
      (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (γ (Multiplicative.ofAdd 0), 1) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd 0), 1)) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd (0 : ℝ))) * u) = GlobalTheory.HeisOrbit.archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
    (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

theorem lie_deriv_polX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    have e : mat (1 : UA σ W.J) = 1 := rfl
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [e, sub_self, smul_zero]
  choose T hT' using fun t : ℝ => GlobalTheory.FockCompactW.exists_op_of_UAt hψ hwe (γ (Multiplicative.ofAdd t), 1) (hγ.2 _) h1W
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add, SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, vacX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        heisX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf f₁ h₁
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFockX

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  atlas_forward_decl GlobalTheory.RealLieFockX.lie_deriv_polX
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactX

open GlobalTheory.RealLift GlobalTheory.FockCompactW

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_left {m p q : Type} [Fintype p] {z : Matrix p q (AE F E)} (hz : At (evI F) z)
    (A : Matrix m p (AE F E)) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (h, 1)) f g) (hf₁ : Acts (evI F) (om (h, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat h * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (h, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (h, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((h, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat h * u) := by
    change mat h * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

theorem pol_stable_compact_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ,
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf f₁ hf₁
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (FockCompactW.heisLine_zero M ψ _)
      (sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_left hu (mat k⁻¹)
      have hv' := at_mul_left hu' (mat k⁻¹)
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_left hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactX

end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.FockCompactX.pol_stable_compact_left | exact GlobalTheory.FockCompactX.pol_stable_compact_left | (intros; apply GlobalTheory.FockCompactX.pol_stable_compact_left <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_orbit_kernel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    Module.rank ℂ ↥(GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relFin om' v ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om' v, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), GlobalTheory.HoweGlobalPair.relFin om' v ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om' v, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p' v ∘ₗ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relFin om' v ≤ LinearMap.ker (Rf.p' v ∘ₗ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om' v, ∀ x ∈ LinearMap.ker (Rf.p' v ∘ₗ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype), g x ∈ LinearMap.ker (Rf.p' v ∘ₗ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).subtype) := by
  first | exact @GlobalTheory.HoweGlobalPair.fin_place_howe_small | exact GlobalTheory.HoweGlobalPair.fin_place_howe_small | (intros; apply GlobalTheory.HoweGlobalPair.fin_place_howe_small <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.RealPlaceSmall

section Ops

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

private theorem acts_zero₀ (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

open scoped Classical in

theorem acts_comb_eq (T : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ h : SInf F κ}
    (hf : Acts (evI F) ⇑T ⇑f ⇑f₁) (hg : Acts (evI F) ⇑T ⇑g ⇑g₁) (hh : Acts (evI F) ⇑T ⇑(c • f + g) ⇑h) :
    h = c • f₁ + g₁ := by
  set g₀ : (κ → Af F) → ℂ := (GlobalTheory.RealLift.intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have e : ∀ φ ψ : SInf F κ, tens (evI F) ⇑(c • φ + ψ) r₀ = c • tens (evI F) ⇑φ r₀ + tens (evI F) ⇑ψ r₀ := by
    intro φ ψ; funext y; simp [tens]; ring
  have key : tens (evI F) ⇑h r₀ = tens (evI F) ⇑(c • f₁ + g₁) r₀ := by
    rw [← hh r₀ (hrest₀ _), e, map_add, map_smul, hf r₀ (hrest₀ f), hg r₀ (hrest₀ g), e]
  ext a
  have := congrFun key (GlobalTheory.RealLift.ptAt a 0)
  rw [htens₀, htens₀, GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt, hg₀0, mul_one, mul_one] at this
  exact this

theorem exists_op {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (Rel : V → V → Prop)
    (hex : ∀ f ∈ P, ∃ f₁ ∈ P, Rel f f₁) (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (hzero : Rel 0 0)
    (hcomb : ∀ (c : ℂ) f f₁ g g₁, f ∈ P → g ∈ P → Rel f f₁ → Rel g g₁ → Rel (c • f + g) (c • f₁ + g₁)) :
    ∃ D : Module.End ℂ ↥P, ∀ x : ↥P, Rel x (D x) := by
  choose d hdP hd using hex
  refine ⟨{ toFun := fun x => ⟨d x x.2, hdP x x.2⟩, map_add' := ?_, map_smul' := ?_ }, fun x => hd x x.2⟩
  · intro x y
    apply Subtype.ext
    have h := hcomb 1 x (d x x.2) y (d y y.2) x.2 y.2 (hd x x.2) (hd y y.2)
    simp only [one_smul] at h
    exact huniq _ _ _ (hd _ (x + y).2) h
  · intro c x
    apply Subtype.ext
    have h := hcomb c x (d x x.2) 0 0 x.2 P.zero_mem (hd x x.2) hzero
    simp only [add_zero] at h
    exact huniq _ _ _ (hd _ (c • x).2) h

end Ops

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem realTransfer' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' Bs.emb, ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    Module.rank ℂ ↥(G.M'.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype), g x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal hLieX hCptX
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  set P := G.M'.Pol Bs.ψ Bs.emb with hPdef

  have lieOp : ∀ γ ∈ Lines σ G.W, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P,
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑(x : SInf F (Fin a' × Fin (a + a')))
        ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a'))) := by
    intro γ hγ
    refine exists_op P (fun f f₁ => ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁)
      (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.1 _ h₁ h₂)
      (GlobalTheory.RealLieOp.actsD_zero' (fun t => om' (1, γ (Multiplicative.ofAdd t))))
      (fun c f f₁ g g₁ _ _ h₁ h₂ => GlobalTheory.RealLieOp.actsD_comb (fun t => om' (1, γ (Multiplicative.ofAdd t))) c h₁ h₂)
    obtain ⟨f₁, h₁⟩ := (hLie γ hγ f hf).1
    exact ⟨f₁, (hLie γ hγ f hf).2 f₁ h₁, h₁⟩
  have cptOp : ∀ k ∈ KInf σ G.W Bs.emb, ∃ D : Module.End ℂ ↥P, ∀ x : ↥P,
      Acts (evI F) (om' (1, k)) ⇑(x : SInf F (Fin a' × Fin (a + a')))
        ⇑((D x : ↥P) : SInf F (Fin a' × Fin (a + a'))) := by
    intro k hk
    refine exists_op P (fun f f₁ => Acts (evI F) (om' (1, k)) ⇑f ⇑f₁)
      (fun f hf => ?_) (fun f f₁ f₂ h₁ h₂ => (GlobalTheory.RealLift.actsLaws F _ f f₁ f₂).2.2.2.1 _ h₁ h₂)
      (acts_zero₀ _) (fun c f f₁ g g₁ hf hg h₁ h₂ => ?_)
    · obtain ⟨f₁, h₁⟩ := (hCpt k hk f hf).1
      exact ⟨f₁, (hCpt k hk f hf).2 f₁ h₁, h₁⟩
    · have hs : c • f + g ∈ P := add_mem (P.smul_mem c hf) hg
      obtain ⟨h, hh⟩ := (hCpt k hk _ hs).1
      have e := acts_comb_eq (om' (1, k)) c h₁ h₂ hh
      rw [e] at hh
      exact hh

  have key : ∀ N : Submodule ℂ ↥P, relInf G.M' Bs.ψ Bs.emb om' ≤ N →
      (∀ g ∈ opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      have h1 : f₁ ∈ P := hLieX γ hγ f hf f₁ hA
      exact ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      have h1 : f₁ ∈ P := hCptX k hk f hf f₁ hA
      exact ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hD⟩ := lieOp γ hγ
      have hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om' := Or.inr ⟨γ, hγ, hD⟩
      have e : f₁ = ((D y : ↥P) : SInf F _) := (GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.1 _ hA (hD y)
      exact ⟨D y, hop D hgD y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hD⟩ := cptOp k hk
      have hgD : D ∈ opInf G.M' Bs.ψ Bs.emb om' := Or.inl ⟨k, hk, hD⟩
      have e : f₁ = ((D y : ↥P) : SInf F _) := (GlobalTheory.RealLift.actsLaws F _ _ _ _).2.2.2.1 _ hA (hD y)
      exact ⟨D y, hop D hgD y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 Bs G.M' hT.base hg.hV' hg.hW hg.hM', ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    exact ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot'.lie γ hγ f hf _ hA
    · show R.p' (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot'.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hgI x hx
    have hx' : R.p' (x : SInf F _) = 0 := hx
    show R.p' ((g x : ↥P) : SInf F _) = 0
    rcases hgI with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have h := hM.real.cpt k hk 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _ (acts_zero₀ _) (hA x)
        (by rw [hx', map_zero])
      rw [map_zero] at h
      exact h.symm
    · have h := hM.real.lie γ hγ 0 (G.M.Pol Bs.ψ Bs.emb).zero_mem x x.2 0 _
        (GlobalTheory.RealLieOp.actsD_zero' _) (hA x) (by rw [hx', map_zero])
      rw [map_zero] at h
      exact h.symm

end GlobalTheory.HoweGlobalPair.RealPlaceSmall

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' Bs.emb, ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    Module.rank ℂ ↥(G.M'.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype), g x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) := by
  atlas_forward_decl GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer'
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobalPair.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F))
  (hvac : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v))
  (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hvac

theorem ext_mem_SB (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl F) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact hvac v

omit hvac in
include hstd in

theorem ext_std (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hstd] with v h1 h2
  rw [h1, h2]

include hstd in

theorem rest_ext (f : SInf F (Fin n × Fin d)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ)

include hstd in

theorem acts_ext [DecidableEq T] (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hstd φ)) ?_
  rw [ext_of_mem]
  exact h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hvac φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobalPair.Transfer

end

noncomputable section

open scoped Classical

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobalPair.Transfer in
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac mem_of_pure mem_of_tprod) in

theorem GlobalTheory.HoweGlobalPair.tensor_transfer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
    (∀ v, M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) →
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ N, GlobalTheory.SquareAgree.IsThetaSubG M ψ emb om N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) [DecidableEq {v // v ∈ T}]
      (L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))) →ₗ[ℂ] ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobalPair.relInf M ψ emb om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ w : T, ∀ x ∈ GlobalTheory.HoweGlobalPair.relFin om w.1, ∀ (x₀ : ↥(M.Pol ψ emb)) (y : ∀ w' : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y w x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf M ψ emb om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ w : T, ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om w.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) ∈ N) := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb om hvac hstd N hN T _ L hL
  have hLe : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin n × Fin d)) (ext M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem M T φ v h)
  have hpA := pure_mem_algD M T hvac (ψ := ψ) emb
  have hR := rest_ext M T hvac hstd
  have hSB := ext_mem_SB M T hvac
  have hV := ext_vac M T
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD M ψ emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)),
        GlobalTheory.HoweGlobalPair.relInf M ψ emb om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.lie γ hγ f hf _ x.2 hD _ (hSB φ) (hV φ)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe]
        exact hN.cpt k hk _ f.2 _ f₁.2 hA _ (hSB φ) (hV φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro w x hx x₀ y
    rw [hLe]
    refine hN.fin w.1 _ _ x₀.2 (hSB _) (hV _) ?_
    rw [ext_of_mem M T _ w, Function.update_self]
    exact hx
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.stabCpt k hk _ ht
    · let S : Submodule ℂ (↥(M.Pol ψ emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add, Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.stabLie γ hγ _ ht _ (hLA _) (hS t)
  · intro w g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w' => (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g w') (φ w')) =
          Function.update φ w (g (φ w)) := by
        funext w'
        by_cases hw : w' = w
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext M T hvac hstd _ φ w (g (φ w)) _ (hA (φ w))]
    rw [e]
    exact hN.stabFin w.1 h hh _ ht

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
    (∀ v, M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) →
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ N, GlobalTheory.SquareAgree.IsThetaSubG M ψ emb om N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) [DecidableEq {v // v ∈ T}]
      (L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))) →ₗ[ℂ] ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobalPair.relInf M ψ emb om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ w : T, ∀ x ∈ GlobalTheory.HoweGlobalPair.relFin om w.1, ∀ (x₀ : ↥(M.Pol ψ emb)) (y : ∀ w' : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y w x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf M ψ emb om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ w : T, ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om w.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) ∈ N) := by
  atlas_forward_decl GlobalTheory.HoweGlobalPair.tensor_transfer
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  classical

  have join : ∀ t₁ t₂ : M₀ ⊗[ℂ] (⨂[ℂ] i, M i),
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ + t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
    rintro t₁ t₂ ⟨m₁, f₁, φ₁, rfl⟩ ⟨m₂, f₂, φ₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      refine ⟨1, fun _ => r • x, fun _ => g, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]
      exact join _ _ h₁ h₂
  | add t₁ t₂ h₁ h₂ => exact join _ _ h₁ h₂

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem stage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      ∀ T : Finset (Pl F), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T → PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hfin hR N hN T hT
  classical
  have hb := hM.triple.base
  have hg := hM.triple.geo
  have hc := hM.triple.chars

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdetV : G.V'.J.det ≠ 0 :=
    det_ne_sig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have hdetW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)

  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a + a') :=
    resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk : GlobalTheory.LFun.IsHecke F E (Xc.α / Xc.β) := hecke_div hc.heckeα hc.heckeβ

  have hLie := GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock F E σ hb.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hb.std
    hg.hV'.herm hdetV hg.hW.skew hdetW hc.resα hres hc.heckeα hhk hM.triple.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock F E σ hb.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hb.std
    hg.hV'.herm hdetV hg.hW.skew hdetW hc.resα hres hc.heckeα hhk hM.triple.weil' Bs.emb hg.hV'.cartan hg.hW.cartan

  obtain ⟨r₀, c₀, k₀, rel₀, st₀⟩ := GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair F E σ Bs a a' G Xc om om' R Rf hM hR hLie hCpt
  have hloc := fun v : T => GlobalTheory.T.matched_maps_orbit_kernel F E σ Bs a a' G Xc om om' R Rf hM hfin v.1

  have hvac : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hg.hM'.vac v).1
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M' Bs.ψ Bs.emb hg.hM'.std T
  obtain ⟨h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer G.M' Bs.ψ Bs.emb om' hvac hg.hM'.std N hN T L hL

  have hdich := GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules (ι := T) (M₀ := ↥(G.M'.Pol Bs.ψ Bs.emb)) (P₀ := R.Pi)
    (M := fun v : T => ↥(SB (Fin a' × Fin (a + a') → Fv F v.1))) (P := fun v : T => Rf.Pi v.1)
    (GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om') (fun v => GlobalTheory.HoweGlobalPair.opFin om' v.1)
    (GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om') (fun v => GlobalTheory.HoweGlobalPair.relFin om' v.1)
    (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)
    (fun v => Rf.p' v.1 ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v.1)).subtype)
    r₀ (fun v => (hloc v).1) c₀ k₀ rel₀ st₀ (fun v => (hloc v).2.1) (fun v => (hloc v).2.2.1)
    (fun v => (hloc v).2.2.2.1) (fun v => (hloc v).2.2.2.2) (N.comap L)
    (fun x hx y => h₁ x hx y) (fun v x hx x₀ y => h₂ v x hx x₀ y) (fun g hg t ht => h₃ g hg t ht)
    (fun v g hg t ht => h₄ v g hg t ht)
  rcases hdich with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦA
    obtain ⟨t, rfl⟩ := hrange hΦA
    have hk : t ∈ LinearMap.ker _ := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := decomp t
    rw [LinearMap.mem_ker, map_sum] at hk

    let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun j v =>
      if h : v ∈ T then (φ j ⟨v, h⟩ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) else G.M'.vac v
    have hin : ∀ j v (h : v ∈ T), φ' j v = φ j ⟨v, h⟩ := fun j v h => dif_pos h
    have hout : ∀ j, ∀ v ∉ T, φ' j v = G.M'.vac v := fun j v h => dif_neg h
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch
    refine ⟨T, hT, 0, m, Fin.elim0, Fin.elim0, fun j => (f j : SInf F _), φ', fun i => i.elim0, fun j => ?_, ?_, ?_, ?_⟩
    · refine ⟨(f j).2, fun v => ?_, hout j⟩
      by_cases h : v ∈ T
      · rw [hin j v h]; exact (φ j ⟨v, h⟩).2
      · rw [hout j v h]; exact hvac v
    · simp
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL (f j) (φ j) (φ' j) (hin j) (hout j)
    · rw [Finset.univ_eq_empty, Finset.sum_empty, ← hk]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearMap.comp_apply, Submodule.subtype_apply]
      refine congrArg (TensorProduct.tmul ℂ (R.p' (f j : SInf F _)))
        (congrArg (PiTensorProduct.tprod ℂ (s := fun v : T => Rf.Pi v.1)) (funext fun v => ?_))
      rw [hin j v.1 v.2]
      rfl

theorem allInKer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hfin hR N hN hne Φ hΦ

  obtain ⟨Ψ, hΨ, hΨN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hN.le hne)

  obtain ⟨T₁, hT₁, hΦ₁⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb (hN.le hΦ) Xc.T
  obtain ⟨T, hT, hΨT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb hΨ T₁
  have hΦT := GlobalTheory.HoweGlobal.algAt_mono G.M' Bs.ψ Bs.emb hT hΦ₁
  rcases stage F E σ Bs a a' G Xc om om' R Rf hM hfin hR N hN T (hT₁.trans hT) with hle | hmatch
  · exact absurd (hle hΨT) hΨN
  · exact hmatch Φ hΦ hΦT

end GlobalTheory.HoweGlobalPair

end
end
