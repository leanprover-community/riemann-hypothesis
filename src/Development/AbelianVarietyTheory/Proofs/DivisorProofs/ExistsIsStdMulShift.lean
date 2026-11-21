import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRangeOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GramOfIsWittBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDoubleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.ArchPull

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

def linM (D : Matrix κ ι F) :
    (ι → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun a := fun k => ∑ i, mixedEmbedding F (D k i) * a i
  map_add' a b := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.smul_sum, mul_smul_comm]

theorem linM_apply (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) (k : κ) :
    linM D a k = ∑ i, mixedEmbedding F (D k i) * a i := rfl

theorem linM_mul (L : Matrix ι κ F) (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) :
    linM L (linM D a) = linM (L * D) a := by
  funext i
  simp only [linM_apply, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem linM_one (a : ι → mixedEmbedding.mixedSpace F) : linM (1 : Matrix ι ι F) a = a := by
  funext i
  simp [linM_apply, Matrix.one_apply]

theorem exists_leftInv (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0) :
    ∃ L : Matrix ι κ F, L * D = 1 := by
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz; exact hD z (by simpa using hz)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' D, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end GlobalTheory.ArchPull

open GlobalTheory.ArchPull in
theorem GlobalTheory.ArchPull.exists_pull : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ,
      ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i) := by
  intro F _ _ ι κ _ _ D hD
  obtain ⟨L, hL⟩ := exists_leftInv D hD
  let M := LinearMap.toContinuousLinearMap (linM D)
  let N := LinearMap.toContinuousLinearMap (linM L)
  have hb : ∀ a, ‖a‖ ≤ ‖N‖₊ * ‖M a‖ := fun a => by
    have e : N (M a) = a := by
      change linM L (linM D a) = a
      rw [linM_mul, hL, linM_one]
    calc ‖a‖ = ‖N (M a)‖ := by rw [e]
      _ ≤ ‖N‖ * ‖M a‖ := N.le_opNorm _
      _ = _ := rfl
  have hl : AntilipschitzWith ‖N‖₊ M := ContinuousLinearMap.antilipschitz_of_bound M hb
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ M.hasTemperateGrowth hl, fun f a => rfl⟩
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.FinPull

theorem pullback_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ w)) ∈
        SB (ι → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ ι κ _ _ D hD g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  set A := algebraMap F (FiniteAdeleRing (𝓞 F) F)
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact hD z (by simpa using hz)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D) (LinearMap.ker_eq_bot.mpr hinj)
  set L := LinearMap.toMatrix' G
  have hLD : L * D = 1 := by
    have : LinearMap.toMatrix' (G ∘ₗ Matrix.toLin' D) = LinearMap.toMatrix' LinearMap.id := by rw [hG]
    simpa [L, LinearMap.toMatrix'_comp] using this
  have hM : Continuous fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hN : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Function.LeftInverse (fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w)
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w) := fun w => by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hLD, Matrix.map_one A (map_zero A) (map_one A), Matrix.one_mulVec]
  exact ⟨hg.1.comp_continuous hM, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding hN hM)⟩

end GlobalTheory.FinPull
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem pureA_mulVec_glue (D : Matrix κ ι F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F ι × Vf F ι) :
    pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p) =
      f (fun k => ∑ i, mixedEmbedding F (D k i) * eI F ι p.1 i) *
      g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  unfold pureA
  congr 2 <;> funext k
  · refine ((map_sum ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
        (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (map_mul _ _ _).trans ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (D k i)) *
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F ι p.1 i)) = _
    rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem pureA_glue_eq (D : Matrix κ ι F)
    (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (hT : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) =
      fun p => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) p.1 *
        g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  funext p
  rw [pureA_mulVec_glue, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]

theorem integrable_glue (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Integrable (fun p : Vi F ι × Vf F ι => Φ (D.map (algebraMap F (AF F)) *ᵥ glue p)) (mu F ι) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [pureA_glue_eq D T hT f g]
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f)).integrable.mul_prod
      (integrable_SB (GlobalTheory.FinPull.pullback_mem_SB F ι κ D hD g hg))
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

theorem integral_pull_injective : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ Φ ∈ schA F κ, (letI : MeasurableSpace (ι → AF F) := borel _;
        Integrable (fun w => Φ (D.map (algebraMap F (AF F)) *ᵥ w)) ν)) ∧
      ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (letI : MeasurableSpace (ι → AF F) := borel _;
          ∫ w, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ w) ∂ν) = T f := by
  intro F _ _ ι κ _ _ D hD ν hν
  letI : MeasurableSpace (ι → AF F) := borel _
  haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hν
  haveI : ((mu F ι).map (glueE F ι)).IsAddHaarMeasure := (glueE F ι).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ν ((mu F ι).map (glueE F ι))
  set c := Measure.addHaarScalarFactor ν ((mu F ι).map (glueE F ι))
  have me := (glueE F ι).toHomeomorph.measurableEmbedding
  refine ⟨fun Φ hΦ => ?_, fun g hg => ?_⟩
  · rw [h]
    refine Integrable.smul_measure_nnreal ?_
    exact me.integrable_map_iff.2 (integrable_glue D hD hΦ)
  · obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
    refine ⟨(((c : ℝ) : ℂ) * ∫ v, g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v) ∂(Measure.addHaar : Measure (Vf F ι))) •
      ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι))).comp
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι)).comp T)), fun f => ?_⟩
    rw [h, integral_smul_nnreal_measure]
    change c • ∫ x, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ x) ∂((mu F ι).map (glueE F ι).toHomeomorph) = _
    rw [me.integral_map]
    have e := pureA_glue_eq D T hT f g
    change c • ∫ p, (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) p ∂(mu F ι) = _
    rw [e, mu, integral_prod_mul (fun u : Vi F ι => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) u)
      (fun v : Vf F ι => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v))]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      smul_eq_mul, NNReal.smul_def, Complex.real_smul]
    ring

end GlobalTheory
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblIntw

theorem symp_dblGram_right {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (ξ : A) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin d) (Fin d) A) (u v : Matrix (Fin n) (Fin (d + d)) A) :
    symp c ξ J (dblGram finSumFinEquiv J') u v =
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inl)) (v.submatrix id (finSumFinEquiv ∘ Sum.inl)) -
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inr)) (v.submatrix id (finSumFinEquiv ∘ Sum.inr)) := by
  simp only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, map_add,
    map_neg, id, Function.comp_apply, Finset.sum_add_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_dblEquiv {σ : E →ₐ[F] E} {n d : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)) :
    ∃ D : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      (Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F), ∀ u, D u = dblE co' u := by
  let S : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin (d + d)) (AF F) (AE F E)).trans
      (((LinearEquiv.funCongrLeft (AF F) (Fin n → AE F E) finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)).trans
        ((Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E)).prodCongr
          (Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E))))
  let G : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  refine ⟨S.trans ((co'.e.prodCongr co'.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u => ?_⟩
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem rat_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m k : ℕ)
    (ι : Type) [Fintype ι] (e : Matrix (Fin m) (Fin k) (AE F E) ≃ₗ[AF F] (ι → AF F) × (ι → AF F)),
    (∀ x : Matrix (Fin m) (Fin k) E, ∃ y z : ι → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ y z : ι → F, ∃ x : Matrix (Fin m) (Fin k) E,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro F E _ _ _ _ _ m k ι _ e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin m) (Fin k) E →ₗ[F] Matrix (Fin m) (Fin k) (AE F E) :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  let L : Matrix (Fin m) (Fin k) E →ₗ[F] (ι → AF F) × (ι → AF F) := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (incM F x) := fun x => rfl
  let r : (ι → F) →ₗ[F] (ι → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((ι → F) × (ι → F)) →ₗ[F] (ι → AF F) × (ι → AF F) := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin k) * Module.finrank F E = Fintype.card ι + Fintype.card ι := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩

theorem rat_symp : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (G : ((ι → AF F) × (ι → AF F)) →ₗ[AF F] ((ι → AF F) × (ι → AF F))),
    (∀ y z : ι → F, ∃ y' z' : ι → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i))) →
    (∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
    ∃ a : Matrix (ι ⊕ ι) (ι ⊕ ι) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
  intro F _ _ ι _ _ G hrat hω
  let P : (ι ⊕ ι → AF F) ≃ₗ[AF F] (ι → AF F) × (ι → AF F) := LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let Gs : (ι ⊕ ι → AF F) →ₗ[AF F] (ι ⊕ ι → AF F) := P.symm.toLinearMap ∘ₗ G ∘ₗ P.toLinearMap
  have hP : ∀ w : (ι → AF F) × (ι → AF F), P.symm w = Sum.elim w.1 w.2 := fun w => by
    funext k; rcases k with k | k <;> rfl
  have hP' : ∀ v : ι ⊕ ι → AF F, P v = (v ∘ Sum.inl, v ∘ Sum.inr) := fun v => rfl
  have hGs : ∀ v, Gs v = Sum.elim (G (P v)).1 (G (P v)).2 := fun v => hP _
  have hent : ∀ i j, ∃ q : F, LinearMap.toMatrix' Gs i j = algebraMap F (AF F) q := by
    intro i j
    obtain ⟨y', z', h⟩ := hrat ((Pi.single j (1 : F)) ∘ Sum.inl) ((Pi.single j (1 : F)) ∘ Sum.inr)
    refine ⟨Sum.elim y' z' i, ?_⟩
    have hs : (Pi.single j (1 : AF F) : ι ⊕ ι → AF F) = fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : ι ⊕ ι → F) k) := by
      funext k; by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [LinearMap.toMatrix'_apply, hs, hGs, hP']
    let w0 : (ι → AF F) × (ι → AF F) := (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inl) k),
      fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inr) k))
    change Sum.elim (G w0).1 (G w0).2 i = _
    rw [show G w0 = _ from h]
    rcases i with i | i <;> rfl
  choose a' ha using hent
  let a : Matrix (ι ⊕ ι) (ι ⊕ ι) F := Matrix.of a'
  have hM : a.map (algebraMap F (AF F)) = LinearMap.toMatrix' Gs := by ext i j; exact (ha i j).symm
  have hact : ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
    intro w
    rw [hM, GlobalTheory.RatWeilOp.act, LinearMap.toMatrix'_mulVec, hGs, hP']
    rw [show ((Sum.elim w.1 w.2) ∘ Sum.inl, (Sum.elim w.1 w.2) ∘ Sum.inr) = w from Prod.ext rfl rfl]
    rfl
  refine ⟨a, ?_, hact⟩
  have hJ : ∀ v v' : ι ⊕ ι → AF F,
      v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) *ᵥ v') =
        (v ∘ Sum.inl) ⬝ᵥ (v' ∘ Sum.inr) - (v' ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    intro v v'
    have hJA : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) =
        Matrix.fromBlocks 0 1 (-1) 0 := by
      ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite (algebraMap F (AF F))]
    rw [hJA, Matrix.fromBlocks_mulVec, ← Sum.elim_comp_inl_inr v, sumElim_dotProduct_sumElim]
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, dotProduct_neg,
      Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_comm (v' ∘ Sum.inl)]
    ring
  have hinj : Function.Injective (Matrix.map · (algebraMap F (AF F)) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) F → Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective _ _)
  apply hinj
  simp only
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM]
  have key : ∀ (X : Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) i j, X i j = Pi.single i 1 ⬝ᵥ (X *ᵥ Pi.single j 1) := fun X i j => by
    simp [Matrix.mulVec_single_one]
  refine Matrix.ext fun i j => (key _ i j).trans (Eq.trans ?_ (key _ i j).symm)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hJ, hJ, hGs, hGs]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hω]
  rfl

theorem op_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ} {ei : SInf F κ →L[ℂ] SInf F κ}
    {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ} (h : GlobalTheory.RatWeilOp.IsOp ψ a e c ei ev) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  have hspan := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F κ g hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    have hφF : GlobalTheory.RatWeilOp.IsFam φ := ⟨hφ, hs⟩
    have h2 := h.isFam hφF
    obtain ⟨T, hT⟩ := hl (fun y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i))
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ h2.1 h2.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h2.1 h2.2⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l (h.2.2.2.2.2 f φ hφF).1
  | zero =>
    refine ⟨0, fun f => ?_⟩
    rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _, map_zero]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ + T₂, fun f => ?_⟩
    rw [show pureA F f (x + y) = pureA F f x + pureA F f y from funext fun _ => mul_add _ _ _, map_add, h₁, h₂]
    rfl
  | smul r x _ hx =>
    obtain ⟨T₁, h₁⟩ := hx
    refine ⟨r • T₁, fun f => ?_⟩
    rw [show pureA F f (r • x) = r • pureA F f x from funext fun _ => mul_left_comm _ _ _, map_smul, h₁]
    rfl

theorem doubling_intertwiner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₂ : Matrix (Fin (d + d)) (Fin (d + d)) E),
    JW₂ = dblGram finSumFinEquiv JW →
    ∀ co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW₂)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (e : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ)) (c : ℂ), c ≠ 0 ∧
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE co' u) Ψ) = co.rho B.ψ u (e Ψ)) ∧
      ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), thetaSum F (e Ψ) = c * thetaSum F Ψ := by
  intro F E _ _ _ _ _ σ B hB n d JX JW JW₂ hJ co' hco' co hco
  classical
  let τ : (Fin n × Fin d ⊕ Fin n × Fin d) ≃ Fin n × Fin (d + d) :=
    (Equiv.prodSumDistrib (Fin n) (Fin d) (Fin d)).symm.trans ((Equiv.refl _).prodCongr finSumFinEquiv)
  obtain ⟨D, hD⟩ := exists_dblEquiv co'
  let Rr : ((Fin n × Fin (d + d) → AF F) × (Fin n × Fin (d + d) → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F)) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) τ).prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) τ)
  let G := (D.symm.trans co.e).trans Rr
  have hG : ∀ u, G (D u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := fun u => by
    simp only [G, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; rfl
  have hdot : ∀ p q : Fin n × Fin (d + d) → AF F, (p ∘ τ) ⬝ᵥ (q ∘ τ) = p ⬝ᵥ q := fun p q => by
    simp only [dotProduct]; exact τ.sum_comp (fun i => p i * q i)
  have hGrat : ∀ y z : Fin n × Fin d ⊕ Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d ⊕ Fin n × Fin d → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x₁, h₁⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inl) (z ∘ Sum.inl)
    obtain ⟨x₂, h₂⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inr) (-(z ∘ Sum.inr))
    let x : Matrix (Fin n) (Fin (d + d)) E := fun i j => Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm j)
    have ht : topC (incM F x) = incM F x₁ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hb : botC (incM F x) = incM F x₂ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hx : D (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
      rw [hD, dblE, ht, hb, h₁, h₂]
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> simp
    obtain ⟨y', z', h⟩ := hco x
    exact ⟨y' ∘ τ, z' ∘ τ, by rw [← hx, hG, h]; rfl⟩
  have hGω : ∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := by
    intro w w'
    obtain ⟨u, rfl⟩ := D.surjective w
    obtain ⟨u', rfl⟩ := D.surjective w'
    rw [hG, hG, hdot, hdot, ← co.form, hJ, GlobalTheory.DefDoubling.incM_dblGram, symp_dblGram_right, co'.form, co'.form,
      hD, hD]
    simp only [dblE, topC, botC, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct]
    ring
  obtain ⟨a, ha, hGa⟩ := rat_symp F _ G.toLinearMap hGrat hGω
  obtain ⟨e₀, c, ei, ev, h⟩ := GlobalTheory.RatWeilOp.hasOp_of_symplectic hB.cm.1 hB.std a ha
  have hR : Set.BijOn (GlobalTheory.DblBox.reix (R := AF F) τ) (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _)
      (schA F (Fin n × Fin (d + d)) : Set _) :=
    ⟨fun φ hφ => GlobalTheory.DblBox.reix_mem_schA τ hφ, (GlobalTheory.DblBox.reix τ).injective.injOn,
      fun Φ hΦ => ⟨(GlobalTheory.DblBox.reix τ).symm Φ, by rw [GlobalTheory.DblBox.reix_symm]; exact GlobalTheory.DblBox.reix_mem_schA τ.symm hΦ,
        (GlobalTheory.DblBox.reix τ).apply_symm_apply Φ⟩⟩
  refine ⟨(GlobalTheory.DblBox.reix τ).toLinearMap ∘ₗ e₀, c, h.1, hR.comp (h.bijOn hB.std), fun l hl => ?_, fun u Ψ hΨ => ?_,
    fun Ψ hΨ => ?_⟩
  · exact op_adm h _ (GlobalTheory.DblBox.comp_reix_mem_adm τ hl)
  · have h1 : GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) (dblE co' u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := by
      rw [← hD, ← hG u]; exact (hGa _).symm
    have h2 := GlobalTheory.DblBox.schr_reix B.ψ τ ((co.e u).1 ∘ τ) ((co.e u).2 ∘ τ) (e₀ Ψ)
    have h3 : ∀ p : Fin n × Fin (d + d) → AF F, p ∘ τ ∘ τ.symm = p := fun p => by
      funext k; simp
    rw [Function.comp_assoc, Function.comp_assoc, h3, h3] at h2
    rw [LinearMap.comp_apply, h.Heisenberg₂ _ Ψ hΨ, h1, LinearEquiv.coe_coe, ← h2, Darboux.rho]
    rfl
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, GlobalTheory.DblBox.thetaSum_reix, h.theta Ψ hΨ]

end GlobalTheory.DblIntw

end
end

section
noncomputable section

namespace GlobalTheory.ThK.LiftPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def rtr {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (x : UA σ J) (u : UA σ J → ℂ) : UA σ J → ℂ := fun y => u (y * x)

def trSpan {G : Type} [Group G] {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (L : G →* UA σ J) (f : UA σ J → ℂ) :
    Submodule ℂ (UA σ J → ℂ) :=
  Submodule.span ℂ (Set.range fun g => rtr (L g) f)

def liftSk (h : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) : GL (Fin m) (Fv F v) →* UA σ J :=
  GlobalTheory.SplitUnitLift.liftU h τ J (-1) (fun i j => by rw [hJ, map_neg, map_one, neg_one_mul])
    (by rw [show (J.map τ).det = τ J.det from (AlgHom.map_det τ J).symm]; exact isUnit_iff_ne_zero.2 ((map_ne_zero τ).2 hd))

def thPair {n m : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)) (g : UA σ JX) (μ : Measure (UA σ JY))
    (𝓕 : Set (UA σ JY)) (u : UA σ JY → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) : ℂ :=
  ∫ h in 𝓕, u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldLP (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

def modelA {v : Pl F} (α : (Fv F v)ˣ →* ℂˣ) (n : ℕ) {m : ℕ} (h : GL (Fin m) (Fv F v))
    (Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) : Matrix (Fin n) (Fin m) (Fv F v) → ℂ := fun X =>
  (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
    ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
    Ψ (X * ((h⁻¹ : GL (Fin m) (Fv F v)) : Matrix (Fin m) (Fin m) (Fv F v))ᵀ)

end GlobalTheory.ThK.LiftPair

end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_orbit_decay : GlobalTheory.ThK.KP → GlobalTheory.ThK.SoDecay := by
  first | exact @GlobalTheory.ThKSoDecay.soDecay | exact GlobalTheory.ThKSoDecay.soDecay | (intros; apply GlobalTheory.ThKSoDecay.soDecay <;> assumption)
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKContSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
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

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_big (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_small (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem measure_fundamental_domain_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) (μ : @Measure H (borel H))
    (hμ : @Measure.IsHaarMeasure H _ _ (borel H) μ) (D : Set H)
    (hD : letI := borel H; IsFundamentalDomain
      ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H) D μ) :
    μ D < ⊤ := by
  subst hH
  letI : MeasurableSpace (HR (AF F) σ J) := borel _
  haveI : BorelSpace (HR (AF F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, -, hcov, -, hvol, -⟩ := GlobalTheory.SiegelSet.exists_cover hS hσ hJ
  set Γ := (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf (HR (AF F) σ J)
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  haveI : Countable Γ := by
    have : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
      (MonoidHom.rangeRestrict_surjective _).countable
    exact Function.Injective.countable (f := fun γ : Γ =>
      (⟨γ.1.1, γ.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
      fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  haveI : MeasurableConstSMul Γ (HR (AF F) σ J) := ⟨fun γ => (continuous_mul_left γ.1).measurable⟩
  haveI : SMulInvariantMeasure Γ (HR (AF F) σ J) μ := ⟨fun γ s _ => measure_preimage_mul μ γ.1 s⟩
  refine lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun g => ?_)) (hvol μ hμ)
  obtain ⟨γ, ⟨δ, -, hδ⟩, s, hs, e⟩ := hcov g
  let γ' : Γ := ⟨γ, δ, hδ⟩
  refine ⟨γ'⁻¹, ?_⟩
  have : γ'⁻¹ • g = s := inv_smul_eq_iff.2 e
  rw [this]; exact hs

theorem measure_dom_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : B.IsGood σ) {n d r s : ℕ} {Y : Spc F E n} {W : Spc F E d}
    (hY : Y.IsHerm σ B r s) {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) : M.μ M.dom < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (hY.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hJ : IsHermND σ ((1 : E) • Y.J.map σ) := by
    rw [one_smul]
    refine ⟨fun i j => congrArg σ (hY.herm i j), ?_⟩
    have e : (Y.J.map σ).det = σ Y.J.det := ((σ : E →+* E).map_det _).symm
    rw [e]
    exact (map_ne_zero σ).2 hd
  exact measure_fundamental_domain_lt_top hS hB.cm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ one_ne_zero) M.μ hM.haar M.dom hM.dom

theorem contSmall : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT Φ' hΦ'
  have hPair := isPair_small hT
  have hSo : Φ' ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ').2
  have hS : Φ' ∈ schA F _ := so_le_schA hT.geo.hM' _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ' hS
  refine ⟨?_, fun γ hγ h => ?_⟩
  · obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ' hSo 0
    haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
    have hv := measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
    have hht : Continuous (fun h : UA σ G.W.J => (ht h : ℝ)) :=
      NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : SecondCountableTopology (AE F E) := by
      obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
      exact e.secondCountableTopology
    haveI hMat : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin (a + a') → Fin (a + a') → AE F E))
    haveI : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))).symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin (a + a')) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    haveI : SecondCountableTopology (UA σ G.W.J) :=
      (Topology.IsEmbedding.subtypeVal (p := fun x : GL (Fin (a + a')) (AE F E) => x ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J))).secondCountableTopology
    haveI : FirstCountableTopology (UA σ G.W.J) :=
      TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    rw [continuous_iff_continuousAt]
    intro h₀
    have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 :=
      hht.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    unfold Model.I
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun g => ?_
      have h1 := hC g h
      rw [pow_zero, mul_one] at h1
      calc ‖theta om' Φ' g h‖ ≤ C * (ht h : ℝ) ^ k := h1
        _ ≤ max C 0 * (ht h : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh.le _) (le_max_right _ _)
    · exact integrableOn_const hv.ne
    · exact Eventually.of_forall fun g =>
        (hB.1.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e := hB.2.1 1 (one_mem _) γ hγ g h
    rw [one_mul] at e
    exact e

end GlobalTheory.ThKContSmall

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct NNReal

namespace GlobalTheory.ThK.PairConv

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_herm_of_skew (hCM : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) : ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • J.map σ) := by
  obtain ⟨x, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hCM
  have hss := GlobalTheory.SiegelSet.sigma_sigma hCM
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sub, hss]
    rw [hJ j i]
    ring
  · have hdet : (J.map σ).det = σ J.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_smul, hdet]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))) ((map_ne_zero_iff σ σ.toRingHom.injective).2 hd)

theorem exists_rat_ht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) :
    ∃ γ ∈ ratU σ J, (ht (γ * h) : ℝ) ≤ 2 * qht h := by
  have h1 : (1 : ℝ≥0) ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  have h2 : qht h < 2 * qht h := by
    rw [two_mul]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h2
  exact ⟨γ.1, γ.2, by exact_mod_cast hγ.le⟩

theorem thetaSum_moderateGrowth (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {n m : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)) {χX χY : Chr F E}
    {om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)}
    (hW : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om)
    {Φ : (Fin n × Fin m → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin m)) :
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖thetaSum F (om (g, h) Φ)‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  obtain ⟨v, -, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hcm ∅
  let B : Base F E := ⟨ψ, fun w => Classical.choice inferInstance, 0, 0, ∅, fun v => absurd v.2 (Finset.notMem_empty _), v, τ⟩
  let X : Spc F E n := ⟨JX, ⊥, 0, 1⟩
  let Y : Spc F E m := ⟨JY, ⊥, 0, 1⟩
  exact GlobalTheory.ThetaFree.theta_moderateGrowth F E σ B n m X Y ⟨co, fun _ => 0, 0, ∅⟩ χX χY om ⟨hψ, hW⟩ Φ hΦ

end

theorem integrableOn_mul_conj_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.ThK.KP → ∀ (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → ∀ (hY : ∀ i j, σ (JY j i) = -JY i j) (hYd : JY.det ≠ 0) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)), (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F, co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) → ∀ χX χY : Chr F E, IsHecke F E χX → IsHecke F E χY → ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om → ∀ f : UA σ JY → ℂ, Continuous f → (∀ γ ∈ ratU σ JY, ∀ h, f (γ * h) = f h) → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (g : UA σ JX) (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ JY) 𝓕 μ → IntegrableOn (fun h => f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
  intro F E _ _ _ _ _ σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW f hfc _ hdec Φ hΦ g μ 𝓕 hμ h𝓕
  have hS := hW.isUSplitting
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c₀, hc₀, hJ⟩ := exists_herm_of_skew hcm hY hYd
  have heq := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := JY) hσ hc₀
  haveI : BorelSpace (UA σ JY) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hK.siegelSetUnitary hcm hJ _ heq μ hμ 𝓕 h𝓕).ne
  have hcont : Continuous fun h : UA σ JY => thetaSum F (om (g, h) Φ) := by
    obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin m)
    have h1 : Continuous fun x : UA σ JX × UA σ JY => thetaSum F (om x Φ) :=
      (hS.cont l hl Φ hΦ).congr fun x => hlt _ (hS.pres _ _ hΦ)
    exact h1.comp (continuous_const.prodMk continuous_id)
  have hinv : ∀ γ ∈ ratU σ JY, ∀ h, thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := by
    intro γ hγ h
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW 1 (one_mem _) γ hγ _
      (hS.pres _ _ hΦ)
  obtain ⟨C, k, hC⟩ := thetaSum_moderateGrowth hcm hψ co hW hΦ
  obtain ⟨D, hD⟩ := hdec k
  refine Integrable.of_bound (hfc.mul (Complex.continuous_conj.comp hcont)).aestronglyMeasurable
    (max C 0 * ((ht g : ℝ) * 2) ^ k * D) (.of_forall fun h => ?_)
  obtain ⟨γ, hγ, hγh⟩ := exists_rat_ht_le h
  have hg0 : (0 : ℝ) ≤ ht g := NNReal.coe_nonneg _
  have b : ‖thetaSum F (om (g, h) Φ)‖ ≤ max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k := by
    rw [← hinv γ hγ h]
    refine (hC g _).trans ?_
    have h0 : (0 : ℝ) ≤ (ht g : ℝ) * ht (γ * h) := mul_nonneg hg0 (NNReal.coe_nonneg _)
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hγh hg0) k) (pow_nonneg h0 _)
      (le_max_right _ _)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖thetaSum F (om (g, h) Φ)‖ ≤ ‖f h‖ * (max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k) :=
        mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = max C 0 * ((ht g : ℝ) * 2) ^ k * (‖f h‖ * (qht h : ℝ) ^ k) := by
        rw [← mul_assoc (ht g : ℝ), mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hD h) (mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _))

end GlobalTheory.ThK.PairConv

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow
namespace GlobalTheory.StdRescale

theorem exists_isStd_mulShift : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∃ a : F, a ≠ 0 ∧ IsStd (ψ.mulShift (algebraMap F (AF F) a)) := by
  intro F _ _ hF ψ h
  haveI := hF
  obtain ⟨a₀, ha₀, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling h
  have him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0 := fun w x => by
    have := congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)
    simpa using this.symm
  have hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1 := fun w => by
    have := congrArg Complex.re
      (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])
    rw [map_mul, Complex.mul_re, him, him, mul_zero, sub_zero] at this
    simpa using this
  refine ⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩
  · exact h.1.comp (continuous_const.mul continuous_id)
  · intro x
    rw [AddChar.mulShift_apply, ← map_mul]
    exact h.2.2.1 _
  · intro b hb
    have hu : evI F (pairA F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have hb2 : b.2 = 0 := by
      have h0 := congrArg Prod.snd (hb (pairA F 0 1) hu)
      change (1 : Af F) * b.2 = 0 at h0
      rwa [one_mul] at h0
    have e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0 := by
      refine Prod.ext rfl ?_
      change (algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0
      rw [hb2, mul_zero]
    have hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re *
        (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re =
        -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re := fun w => by
      rw [show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him,
        zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]
    rw [AddChar.mulShift_apply, e1]
    show psiInf F ψ _ = _
    rw [hinf, GlobalTheory.WrongSignPair.trace_evI]
    simp only [hterm, Finset.sum_neg_distrib]
    push_cast
    ring_nf

end GlobalTheory.StdRescale
end
