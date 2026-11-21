import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchExponentEqZeroOfMulSelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationPairEntirePartBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSetIntegralIoiOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ThetaCScalCEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTranslatedIntegrand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntLtrSubThetaCConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolCharOneEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.SgOneOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JMapVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemStabLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapScalarVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TriangularLowerRightDiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsParComap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapHalfTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleMapMemIntAdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionEmbeddingAlgebraMapOfTotallyReal
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGallery
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativityStatement

section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem thetaC_scalC_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (δ : kˣ) (a : IdeleGroup k) :
    thetaC F (scalC (diagonal k δ * a)) = thetaC F (scalC a) := by
  unfold thetaC
  have hv : ∀ ξ : ι → k, ((scalC (IdeleGroup.diagonal k δ * a) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ
      = ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV (δ • ξ) := by
    intro ξ
    funext i
    simp [scalC, ratV, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, IdeleGroup.diagonal,
      Units.smul_def, mul_comm, mul_left_comm]
  simp_rw [hv]
  exact (MulAction.toPerm δ).tsum_eq (fun ξ => F (((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))

noncomputable def thetaCIntegrand (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup k) : ℂ :=
  thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem thetaCIntegrand_mul_diagonalToNormOne (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (ξ : kˣ) (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t (u * diagonalToNormOne k ξ) = thetaCIntegrand w F ω t u := by
  unfold thetaCIntegrand
  have hc : ((u * diagonalToNormOne k ξ : normOneSubgroup k) : IdeleGroup k) =
      IdeleGroup.diagonal k ξ * (u : IdeleGroup k) := by
    rw [Subgroup.coe_mul, mul_comm]
    rfl
  rw [hc, ← mul_assoc, mul_comm (moduleSection w t), mul_assoc, thetaC_scalC_diagonal_mul, map_mul,
    HeckeCharacter.toIdele_diagonal, one_mul]

theorem thetaCIntegrand_inv (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t⁻¹ u =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ := by
  unfold thetaCIntegrand
  rw [EpsteinRankN.Hd.thetaC_scalC_eq hF]
  have e1 : (moduleSection w t⁻¹ * (u : IdeleGroup k))⁻¹ =
      moduleSection w t * ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) := by
    rw [map_inv, mul_inv, inv_inv, Subgroup.coe_inv, mul_comm]
  have e2 : ideleModule k (moduleSection w t⁻¹ * (u : IdeleGroup k)) = t⁻¹ := by
    rw [map_mul, ideleModule_moduleSection, MonoidHom.mem_ker.mp u.2, mul_one]
  have e3 : (((ω⁻¹).toIdele ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) : ℂ)) =
      ((ω.toIdele (u : IdeleGroup k) : ℂ)) := by
    have h : ∀ x, (ω⁻¹) x = (ω x)⁻¹ := fun x => rfl
    simp [HeckeCharacter.toIdele, h]
  rw [e1, e2, e3]
  have e4 : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := by simp
  rw [e4]
  push_cast
  rw [inv_pow, inv_inv]
  ring

theorem theta_integral_functional_equation (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) :
    thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t := by
  have hD := isFundamentalDomain_normOneFundamentalDomain k (normOneMeasure k)
  have hDinv : IsFundamentalDomain (↥(diagonalNormOne k).op)
      ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k) (normOneMeasure k) := by
    refine hD.preimage_of_equiv
      (Measure.measurePreserving_inv (normOneMeasure k)).quasiMeasurePreserving
      inv_involutive.bijective (fun g x => ?_)
    show (g⁻¹ • x)⁻¹ = g • x⁻¹
    rw [Subgroup.smul_def, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop,
      MulOpposite.smul_eq_mul_unop, Subgroup.coe_inv, MulOpposite.unop_inv, _root_.mul_inv_rev,
      inv_inv]
    exact mul_comm _ _
  have hinvar : ∀ (g : ↥(diagonalNormOne k).op) (x : normOneSubgroup k),
      thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t (g • x) =
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t x := by
    intro g x
    have hm : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) ∈ diagonalNormOne k := g.2
    obtain ⟨ξ, hξ⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hm)
    have hg : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) = diagonalToNormOne k ξ :=
      Subtype.ext hξ.symm
    rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, hg, thetaCIntegrand_mul_diagonalToNormOne]
  have hms := measurableSet_normOneFundamentalDomain (K := k)
  have step1 : thetaCInt w F ω t⁻¹ = ((t : ℝ) : ℂ) ^ Fintype.card ι *
      ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k := by
    show ∫ u in normOneFundamentalDomain k, thetaCIntegrand w F ω t⁻¹ u ∂normOneMeasure k = _
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hms (fun u _ => ?_)
    exact thetaCIntegrand_inv w hF ω t u
  have step2 : ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k =
      ∫ u in (fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u ∂normOneMeasure k := by
    rw [← integral_indicator hms, ← integral_indicator (hms.preimage measurable_inv),
      ← integral_inv_eq_self (fun u => ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k).indicator
        (thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t) u) (normOneMeasure k)]
    congr 1
  rw [step1, step2, hDinv.setIntegral_eq hD hinvar]
  rfl

theorem thetaCInt_inv : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}), thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t :=
  fun w _ hF ω t ↦ theta_integral_functional_equation w hF ω t

end GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd
end

section
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinUnfold.Hd

open NumberField.mixedEmbedding
open scoped SchwartzMap Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_schwartzBruhatPi_majorant {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) :
    ∃ G ∈ schwartzBruhatPi k ι, ∃ r : (ι → 𝔸[k]) → ℝ,
      (∀ x, G x = (r x : ℂ)) ∧ ∀ x, ‖F x‖ ≤ r x := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨φ, I, b, rfl⟩ := hH
    obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant φ
    set g : (ι → 𝔸ᶠ[k]) → ℂ := finiteTensor fun i ↦ cosetIndicator I (b i) with hg
    have hgv : ∀ v, g v = (‖g v‖ : ℂ) := by
      intro v
      simp only [hg, finiteTensor]
      rw [norm_prod, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [cosetIndicator_apply]
      split_ifs <;> simp
    refine ⟨schwartzBruhatTensorPi Φ g, schwartzBruhatTensorPi_mem Φ
      (finiteTensor_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat I (b i)),
      fun x ↦ r (infPartPi x) * ‖g (finPartPi x)‖, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp only [schwartzBruhatTensorPi]
      rw [hΦ, Complex.ofReal_mul, ← hgv]
    · simp only [schwartzBruhatTensorPi, norm_mul]
      exact mul_le_mul_of_nonneg_right (hr _) (norm_nonneg _)
  | zero => exact ⟨0, zero_mem _, 0, by simp, by simp⟩
  | add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, m₁, r₁, e₁, b₁⟩ := ih₁
    obtain ⟨G₂, m₂, r₂, e₂, b₂⟩ := ih₂
    refine ⟨G₁ + G₂, add_mem m₁ m₂, r₁ + r₂, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp [e₁, e₂]
    · exact (norm_add_le _ _).trans (add_le_add (b₁ x) (b₂ x))
  | smul c H _ ih =>
    obtain ⟨G, m, r, e, b⟩ := ih
    refine ⟨(‖c‖ : ℂ) • G, Submodule.smul_mem _ _ m, ‖c‖ • r, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp [e]
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (b x) (norm_nonneg _)

theorem single_mem_schwartzBruhat {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (i₀ : ι) :
    (fun t : 𝔸[k] ↦ F (Pi.single i₀ t)) ∈ schwartzBruhat k := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set L : mixedSpace k →L[ℝ] (ι → mixedSpace k) :=
      ContinuousLinearMap.single ℝ (fun _ : ι ↦ mixedSpace k) i₀
    have hL : ∀ u, L u = Pi.single i₀ u := fun u ↦ rfl
    set φ' : 𝓢(mixedSpace k, ℂ) := SchwartzMap.compCLM ℂ L.hasTemperateGrowth
      ⟨1, 1, fun u ↦ by rw [hL, Pi.norm_single, one_mul, pow_one]; linarith⟩ φ
    have hφ' : ∀ u, φ' u = φ (Pi.single i₀ u) := fun u ↦ rfl
    have hcl : Topology.IsClosedEmbedding (fun v : 𝔸ᶠ[k] ↦ (Pi.single i₀ v : ι → 𝔸ᶠ[k])) :=
      Function.LeftInverse.isClosedEmbedding (f := fun x : ι → 𝔸ᶠ[k] ↦ x i₀)
        (fun v ↦ Pi.single_eq_same _ _) (continuous_apply i₀) ((continuous_const (y := (0 : ι → 𝔸ᶠ[k]))).update i₀ continuous_id)
    have hg' : (fun v : 𝔸ᶠ[k] ↦ g (Pi.single i₀ v)) ∈ finiteSchwartzBruhat k := by
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhatPi k).mp hg
      exact mem_finiteSchwartzBruhat.2
        ⟨hlc.comp_continuous hcl.continuous, hcs.comp_isClosedEmbedding hcl⟩
    convert schwartzBruhatTensor_mem φ' hg' using 1
    funext t
    simp only [schwartzBruhatTensorPi, schwartzBruhatTensor, hφ']
    congr 2
    · funext i
      by_cases h : i = i₀
      · subst h
        simp [infPartPi]
      · simp only [infPartPi, Pi.single_eq_of_ne h]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace k)
    · funext i
      by_cases h : i = i₀
      · subst h
        simp [finPartPi]
      · simp only [finPartPi, Pi.single_eq_of_ne h]
        rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

theorem line_mem_schwartzBruhat {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {ξ : ι → k} (hξ : ξ ≠ 0) : (fun t : 𝔸[k] ↦ F (t • ratV ξ)) ∈ schwartzBruhat k := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hξ
  set M : Matrix ι ι k := (1 : Matrix ι ι k).updateCol i₀ ξ with hM
  have hdet : M.det ≠ 0 := by
    have : M.det = ξ i₀ := by
      rw [hM, ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    rw [this]
    exact hi₀
  set A : GL ι 𝔸[k] := Matrix.GeneralLinearGroup.map (algebraMap k 𝔸[k])
    (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet) with hA
  have key : ∀ t : 𝔸[k], (A : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ t = t • ratV ξ := by
    intro t
    funext i
    have hAi : (A : Matrix ι ι 𝔸[k]) i i₀ = algebraMap k 𝔸[k] (ξ i) := by
      simp [hA, Matrix.GeneralLinearGroup.mkOfDetNeZero, hM, Matrix.updateCol_self]
    simp [Matrix.mulVec_single, hAi, ratV, mul_comm]
  have h := single_mem_schwartzBruhat (GlobalTheory.T.linearChange_mem_schwartzBruhatPi hF A) i₀
  simpa only [ltr, key] using h

end SlopeTestRemainingChoices

section Unfold

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem scalC_mulVec (a : IdeleGroup k) (v : ι → 𝔸[k]) :
    ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ v = (a : 𝔸[k]) • v := by
  funext i
  simp [scalC, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem ratV_smul (d : k) (ξ : ι → k) : ratV (d • ξ) = algebraMap k 𝔸[k] d • ratV ξ := by
  funext i
  simp [ratV]

theorem ratV_zero : ratV (0 : ι → k) = 0 := by
  funext i
  simp [ratV]

theorem scalC_mul (a b : IdeleGroup k) : (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b :=
  map_mul (Units.map (Matrix.scalar ι : 𝔸[k] →+* Matrix ι ι 𝔸[k]).toMonoidHom) a b

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  show Continuous fun a : 𝔸[k] ↦ Matrix.scalar ι a
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (X := 𝔸[k]) (n := ι) (A := fun a _ ↦ a) (continuous_pi fun _ ↦ continuous_id)

noncomputable def lineMap (p : kˣ × Projectivization k (ι → k)) : {ξ : ι → k // ξ ≠ 0} :=
  ⟨(p.1 : k) • p.2.rep, smul_ne_zero p.1.ne_zero p.2.rep_nonzero⟩

theorem lineMap_injective : Function.Injective (lineMap (k := k) (ι := ι)) := by
  rintro ⟨d, l⟩ ⟨d', l'⟩ h
  have h' : (d : k) • l.rep = (d' : k) • l'.rep := congrArg Subtype.val h
  have hl : l = l' := by
    rw [← l.mk_rep, ← l'.mk_rep, Projectivization.mk_eq_mk_iff']
    refine ⟨(d : k)⁻¹ * d', ?_⟩
    rw [mul_smul, ← h', smul_smul, inv_mul_cancel₀ d.ne_zero, one_smul]
  subst hl
  have hd : d = d' := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 l.rep_nonzero
    have := congrFun h' j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact Units.ext (mul_right_cancel₀ hj this)
  rw [hd]

theorem lineMap_surjective : Function.Surjective (lineMap (k := k) (ι := ι)) := by
  rintro ⟨ξ, hξ⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k ξ hξ
  refine ⟨(a⁻¹, Projectivization.mk k ξ hξ), Subtype.ext ?_⟩
  show ((a⁻¹ : kˣ) : k) • (Projectivization.mk k ξ hξ).rep = ξ
  rw [← ha, Units.smul_def, smul_smul, Units.inv_mul, one_smul]

noncomputable def lineEquiv : kˣ × Projectivization k (ι → k) ≃ {ξ : ι → k // ξ ≠ 0} :=
  Equiv.ofBijective lineMap ⟨lineMap_injective, lineMap_surjective⟩

theorem countable_proj : Countable (Projectivization k (ι → k)) := by
  haveI : Countable k := countable_numberField k
  exact ((lineEquiv (k := k) (ι := ι)).injective.comp (Prod.mk_right_injective (1 : kˣ))).countable

theorem summable_norm_col {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (h : GL ι 𝔸[k]) :
    Summable fun ξ : ι → k ↦ ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF (isCompact_singleton (x := h))
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ξ ↦ hb h rfl ξ) hu

theorem summable_line {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    Summable fun p : kˣ × Projectivization k (ι → k) ↦
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1)‖ :=
  (lineEquiv (k := k) (ι := ι)).summable_iff.2 ((summable_norm_col hF h).subtype {ξ | ξ ≠ 0})

theorem tsum_finset_le {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (h : GL ι 𝔸[k]) (S : Finset (Projectivization k (ι → k))) :
    ∑' d : kˣ, ∑ l ∈ S, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep))‖ ≤
      ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ := by
  have hf := summable_line hF h
  have h1 : ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ =
      ∑' p : kˣ × Projectivization k (ι → k),
        ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1)‖ :=
    ((lineEquiv (k := k) (ι := ι)).tsum_eq
      fun ξ ↦ ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖).symm
  rw [h1, hf.tsum_prod]
  refine Summable.tsum_le_tsum (fun d ↦ ?_) ?_ hf.prod
  · exact (hf.prod_factor d).sum_le_tsum S fun c _ ↦ norm_nonneg _
  · refine summable_sum fun c _ ↦ ?_
    exact hf.comp_injective (i := fun d : kˣ ↦ (d, c)) fun a b hab ↦ (Prod.mk.inj hab).1

theorem thetaC_sub_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    thetaC F h - F 0 = ∑' ξ : {ξ : ι → k // ξ ≠ 0}, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) := by
  classical
  have hs : Summable fun ξ : ι → k ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) :=
    (summable_norm_col hF h).of_norm
  have h3 := hs.tsum_eq_add_tsum_ite 0
  have h4 : ∑' ξ : {ξ : ι → k // ξ ≠ 0}, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) =
      ∑' ξ : ι → k, if ξ = 0 then 0 else F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) := by
    have := tsum_subtype {ξ : ι → k | ξ ≠ 0} (fun ξ ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))
    refine this.trans (tsum_congr fun ξ ↦ ?_)
    by_cases hξ : ξ = 0 <;> simp [Set.indicator, hξ]
  rw [h4, thetaC, h3, ratV_zero, Matrix.mulVec_zero]
  ring

theorem tsum_tsum_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    ∑' d : kˣ, ∑' l : Projectivization k (ι → k),
        F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep)) = thetaC F h - F 0 := by
  have hf : Summable fun p : kˣ × Projectivization k (ι → k) ↦
      F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1) := (summable_line hF h).of_norm
  rw [thetaC_sub_eq hF, ← (lineEquiv (k := k) (ι := ι)).tsum_eq
    fun ξ ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)]
  exact hf.tsum_prod.symm

noncomputable def Gc (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (x : IdeleGroup k) : ℂ :=
  F ((x : 𝔸[k]) • ratV l.rep) * (ω.toIdele x : ℂ) * ((ideleModule k x : ℝ) : ℂ) ^ z

theorem integrable_Gc {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) {z : ℂ} (hz : 1 < z.re) (l : Projectivization k (ι → k)) :
    Integrable (Gc F ω z l) (ideleMeasure k) :=
  integrable_globalZetaIntegrand (line_mem_schwartzBruhat hF l.rep_nonzero) ω hz

theorem continuous_Gc {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (z : ℂ) (l : Projectivization k (ι → k)) : Continuous (Gc F ω z l) :=
  continuous_zetaIntegrand
    (continuous_of_mem_schwartzBruhat (line_mem_schwartzBruhat hF l.rep_nonzero)) ω z

theorem Gc_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (d : kˣ) (x : IdeleGroup k) :
    Gc F ω z l (diagonal k d * x) =
      F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep)) *
        ((ω.toIdele x : ℂ) * ((ideleModule k x : ℝ) : ℂ) ^ z) := by
  have e : ((diagonal k d * x : IdeleGroup k) : 𝔸[k]) • ratV l.rep =
      ((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep) := by
    rw [scalC_mulVec, ratV_smul, Units.val_mul, coe_diagonal, smul_smul, mul_comm]
  rw [Gc, e, map_mul, HeckeCharacter.toIdele_diagonal, map_mul, ideleModule_diagonal, one_mul,
    one_mul, mul_assoc]

theorem norm_Gc_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (d : kˣ) (x : IdeleGroup k) :
    ‖Gc F ω z l (diagonal k d * x)‖ =
      ‖F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep))‖ *
        (ideleModule k x : ℝ) ^ z.re := by
  rw [Gc_diagonal_mul, norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule k x).2]

theorem exists_bound (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : {x : ℝ // 0 < x}, ∀ u ∈ normOneFundamentalDomain k,
      (1 ≤ (t : ℝ) → ∑' ξ : {ξ : ι → k // ξ ≠ 0},
        ‖F (((scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ
          ratV ξ.1)‖ ≤ ((t : ℝ) ^ r)⁻¹ * M) ∧
      ((t : ℝ) ≤ 1 → ∑' ξ : {ξ : ι → k // ξ ≠ 0},
        ‖F (((scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ
          ratV ξ.1)‖ ≤ ((t : ℝ) ^ Fintype.card ι)⁻¹ * M) := by
  obtain ⟨G, hG, ρ, hGρ, hFρ⟩ := exists_schwartzBruhatPi_majorant hF
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x ↦ (norm_nonneg _).trans (hFρ x)
  have hnorm : ∀ x, ‖G x‖ = ρ x := fun x ↦ by
    rw [hGρ, Complex.norm_real, Real.norm_of_nonneg (hρ0 x)]
  have hφ : Continuous fun u : normOneSubgroup k ↦ (scalC (u : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_scalC.comp continuous_subtype_val
  have hφ' : Continuous fun u : normOneSubgroup k ↦ (scalC (u : IdeleGroup k)⁻¹ : GL ι 𝔸[k]) :=
    continuous_scalC.comp (continuous_inv.comp continuous_subtype_val)
  have hE := isCompact_closure_normOneFundamentalDomain k
  obtain ⟨M₁, h₁⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hG (hE.image hφ) r
  obtain ⟨M₀, h₀⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w (adelicFourierPi_mem_schwartzBruhatPi hG) (hE.image hφ') 0
  set N := Fintype.card ι with hN

  have hsr : ∀ h : GL ι 𝔸[k], Summable fun ξ : ι → k ↦ ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) := by
    intro h
    simpa only [hnorm] using summable_norm_col hG h
  have hsF : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ ≤
      ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) := fun h ↦
    ((summable_norm_col hF h).subtype _).tsum_le_tsum (fun ξ ↦ hFρ _) ((hsr h).subtype _)
  have htail : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) =
      ‖thetaC G h - G 0‖ := by
    intro h
    rw [thetaC_sub_eq hG]
    simp only [hGρ]
    rw [← Complex.ofReal_tsum, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ ↦ hρ0 _)]
  have hall : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) ≤
      ‖thetaC G h‖ := by
    intro h
    have h1 := Summable.tsum_subtype_le (fun ξ : ι → k ↦ ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))
      {ξ | ξ ≠ 0} (fun ξ ↦ hρ0 _) (hsr h)
    refine h1.trans (le_of_eq ?_)
    rw [thetaC]
    simp only [hGρ]
    rw [← Complex.ofReal_tsum, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ ↦ hρ0 _)]
  refine ⟨max (max M₁ (‖adelicFourierPi k G 0‖ + M₀)) 0, le_max_right _ _, fun t u hu ↦
    ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩⟩
  · have hm : u ∈ closure (normOneFundamentalDomain k) := subset_closure hu
    have h2 := h₁ _ (Set.mem_image_of_mem _ hm) t ht
    rw [← scalC_mul] at h2
    refine (hsF _).trans ?_
    rw [htail]
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by have := t.2; positivity))
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have hm : u ∈ closure (normOneFundamentalDomain k) := subset_closure hu
    have ht0 : (0 : ℝ) < t := t.2
    have hT : (1 : ℝ) ≤ ((t⁻¹ : {x : ℝ // 0 < x}) : ℝ) := (one_le_inv₀ t.2).2 ht
    have h2 := h₀ _ (Set.mem_image_of_mem _ hm) t⁻¹ hT
    rw [pow_zero, inv_one, one_mul, map_inv, ← scalC_mul, ← mul_inv] at h2
    have hθ : ‖thetaC (adelicFourierPi k G)
        (scalC (moduleSection w t * (u : IdeleGroup k))⁻¹ : GL ι 𝔸[k])‖ ≤
        ‖adelicFourierPi k G 0‖ + M₀ := by
      have := norm_sub_norm_le
        (thetaC (adelicFourierPi k G)
          (scalC (moduleSection w t * (u : IdeleGroup k))⁻¹ : GL ι 𝔸[k]))
        (adelicFourierPi k G 0)
      linarith
    have hmod : (ideleModule k (moduleSection w t * (u : IdeleGroup k)) : ℝ) = t := by
      have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
      rw [map_mul, ideleModule_moduleSection, hu1, mul_one]
    refine ((hsF _).trans (hall _)).trans ?_
    rw [GlobalTheory.CompanionTheory.EpsteinRankN.Hd.thetaC_scalC_eq hG, hmod, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (hθ.trans ?_) (by positivity)
    exact (le_max_right _ _).trans (le_max_left _ _)

theorem integrable_exp_neg_abs_log {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : {x : ℝ // 0 < x} ↦ Real.exp (-(δ * |Real.log t|))) posRealMeasure := by
  have hc : Continuous fun t : {x : ℝ // 0 < x} ↦ Real.exp (-(δ * |Real.log t|)) := by
    have : Continuous fun t : {x : ℝ // 0 < x} ↦ Real.log t :=
      continuous_subtype_val.log fun r ↦ r.2.ne'
    fun_prop
  rw [posRealMeasure_eq_map_expPos,
    integrable_map_measure hc.aestronglyMeasurable measurable_expPos.aemeasurable]
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(δ * |s|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hδ).congr_fun (fun s hs ↦ ?_) measurableSet_Ioi
    have : |s| = s := abs_of_pos hs
    simp [this]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(δ * |s|))) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hδ 0).congr_fun (fun s hs ↦ ?_) measurableSet_Iic
    have : |s| = -s := abs_of_nonpos hs
    simp [this]
  have h3 := h2.union h1
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
  refine h3.congr (ae_of_all _ fun x ↦ ?_)
  have hlog : Real.log ((expPos x : {x : ℝ // 0 < x}) : ℝ) = x := Real.log_exp x
  simp only [Function.comp_apply, hlog]

theorem pow_bound {σ δ : ℝ} {r n : ℕ} (hδ1 : δ ≤ 1) (hδ2 : δ ≤ σ - n) (hδ : 0 < δ)
    (hr : σ + 1 ≤ r) {t : ℝ} (ht : 0 < t) :
    (1 ≤ t → (t ^ r)⁻¹ * t ^ σ ≤ Real.exp (-(δ * |Real.log t|))) ∧
    (t ≤ 1 → (t ^ n)⁻¹ * t ^ σ ≤ Real.exp (-(δ * |Real.log t|))) := by
  constructor
  · intro h1
    have hL : 0 ≤ Real.log t := Real.log_nonneg h1
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, Real.rpow_def_of_pos ht,
      Real.exp_le_exp, abs_of_nonneg hL]
    nlinarith
  · intro h1
    have hL : Real.log t ≤ 0 := Real.log_nonpos ht.le h1
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, Real.rpow_def_of_pos ht,
      Real.exp_le_exp, abs_of_nonpos hL]
    nlinarith

theorem sum_integral_norm_le (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re)
    (hz1 : 1 < z.re) :
    ∃ B : ℝ, ∀ S : Finset (Projectivization k (ι → k)),
      ∑ l ∈ S, ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k ≤ B := by
  obtain ⟨r, hr⟩ := exists_nat_ge (z.re + 1)
  set δ : ℝ := min (z.re - Fintype.card ι) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ2 : δ ≤ z.re - Fintype.card ι := min_le_left _ _
  obtain ⟨M, hM0, hM⟩ := exists_bound w hF r
  set E := normOneFundamentalDomain k with hE
  haveI : IsFiniteMeasure ((normOneMeasure k).restrict E) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top k⟩
  set V : ℝ := ((normOneMeasure k).restrict E).real Set.univ with hV
  set ρ : {x : ℝ // 0 < x} → ℝ := fun t ↦ M * Real.exp (-(δ * |Real.log t|)) with hρ
  have hρi : Integrable (fun t ↦ V • ρ t) posRealMeasure :=
    ((integrable_exp_neg_abs_log hδ).const_mul M).smul V
  refine ⟨∫ t, V • ρ t ∂posRealMeasure, fun S ↦ ?_⟩
  set ψ : IdeleGroup k → ℝ := fun x ↦ ∑ l ∈ S, ‖Gc F ω z l x‖ with hψdef
  have hψ : Integrable ψ (ideleMeasure k) :=
    integrable_finset_sum _ fun c _ ↦ (integrable_Gc hF ω hz1 c).norm
  have h1 : ∑ l ∈ S, ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k = ∫ x, ψ x ∂ideleMeasure k :=
    (integral_finset_sum _ fun c _ ↦ (integrable_Gc hF ω hz1 c).norm).symm
  have hnn : ∀ x, 0 ≤ ψ x := fun x ↦ Finset.sum_nonneg fun c _ ↦ norm_nonneg _
  rw [h1, integral_ideleMeasure_eq_integral_fundamentalDomain w hψ]
  refine integral_mono_of_nonneg (ae_of_all _ fun t ↦ ?_) hρi (ae_of_all _ fun t ↦ ?_)
  · exact integral_nonneg fun u ↦ tsum_nonneg fun d ↦ hnn _
  · have hpt : ∀ u ∈ E, ∑' ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ≤ ρ t := by
      intro u hu
      set x : IdeleGroup k := moduleSection w t * (u : IdeleGroup k) with hx
      have hmod : (ideleModule k x : ℝ) = t := by
        have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
        rw [hx, map_mul, ideleModule_moduleSection, hu1, mul_one]
      have h2 : ∀ ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) =
          (∑ l ∈ S, ‖F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((ξ : k) • l.rep))‖) *
            (t : ℝ) ^ z.re := by
        intro ξ
        have e : diagonal k ξ * moduleSection w t * (u : IdeleGroup k) = diagonal k ξ * x :=
          mul_assoc _ _ _
        rw [e]
        show ∑ l ∈ S, ‖Gc F ω z l (diagonal k ξ * x)‖ = _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [norm_Gc_diagonal_mul, hmod]
      simp only [h2]
      rw [tsum_mul_right]
      have ht0 : 0 < (t : ℝ) := t.2
      have hp : 0 ≤ (t : ℝ) ^ z.re := Real.rpow_nonneg ht0.le _
      have h3 := tsum_finset_le hF (scalC x) S
      obtain ⟨hb1, hb2⟩ := hM t u hu
      obtain ⟨hc1, hc2⟩ := pow_bound hδ1 hδ2 hδ hr ht0
      rcases le_total 1 (t : ℝ) with h | h
      · calc _ ≤ (((t : ℝ) ^ r)⁻¹ * M) * (t : ℝ) ^ z.re :=
              mul_le_mul_of_nonneg_right (h3.trans (hb1 h)) hp
          _ = M * (((t : ℝ) ^ r)⁻¹ * (t : ℝ) ^ z.re) := by ring
          _ ≤ ρ t := mul_le_mul_of_nonneg_left (hc1 h) hM0
      · calc _ ≤ (((t : ℝ) ^ Fintype.card ι)⁻¹ * M) * (t : ℝ) ^ z.re :=
              mul_le_mul_of_nonneg_right (h3.trans (hb2 h)) hp
          _ = M * (((t : ℝ) ^ Fintype.card ι)⁻¹ * (t : ℝ) ^ z.re) := by ring
          _ ≤ ρ t := mul_le_mul_of_nonneg_left (hc2 h) hM0
    have h4 := integral_mono_of_nonneg (μ := (normOneMeasure k).restrict E)
      (f := fun u : normOneSubgroup k ↦
        ∑' ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)))
      (g := fun _ ↦ ρ t) (ae_of_all _ fun u ↦ tsum_nonneg fun d ↦ hnn _) (integrable_const _)
      ((ae_restrict_iff' (measurableSet_normOneFundamentalDomain k)).2 (ae_of_all _ hpt))
    simpa [hV] using h4

theorem summable_integral_norm_Gc (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Summable fun l : Projectivization k (ι → k) ↦ ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k := by
  obtain ⟨B, hB⟩ := sum_integral_norm_le w hF ω hz hz1
  exact summable_of_sum_le (fun c ↦ integral_nonneg fun x ↦ norm_nonneg _) hB

theorem integrable_tsum_Gc (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Integrable (fun x ↦ ∑' l : Projectivization k (ι → k), Gc F ω z l x) (ideleMeasure k) := by
  haveI := countable_proj (k := k) (ι := ι)
  have hs := summable_integral_norm_Gc w hF ω hz hz1
  have hint := integrable_Gc hF ω hz1
  have hmeas : ∀ c, AEMeasurable (fun x ↦ ‖Gc F ω z c x‖ₑ) (ideleMeasure k) := fun c ↦
    (hint c).aemeasurable.enorm
  have hlin : ∫⁻ x, ∑' c, ‖Gc F ω z c x‖ₑ ∂ideleMeasure k ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have : ∀ c, ∫⁻ x, ‖Gc F ω z c x‖ₑ ∂ideleMeasure k =
        ENNReal.ofReal (∫ x, ‖Gc F ω z c x‖ ∂ideleMeasure k) := fun c ↦
      (ofReal_integral_norm_eq_lintegral_enorm (hint c)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun c ↦ integral_nonneg fun _ ↦ norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨(Measurable.tsum fun c ↦ (continuous_Gc hF ω z c).measurable).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm)
    (lt_top_iff_ne_top.2 hlin)

theorem integrableOn_thetaC_mul {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (a : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC F (scalC (a * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      (scalC (a * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_scalC.comp (continuous_const.mul continuous_subtype_val)
  have hθ : ContinuousOn (thetaC F) ((fun u : normOneSubgroup k ↦
      (scalC (a * (u : IdeleGroup k)) : GL ι 𝔸[k])) '' closure (normOneFundamentalDomain k)) := by
    obtain ⟨v, hv, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF (hE.image hφ)
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hv fun ξ h hh ↦ hb h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦ thetaC F (scalC (a * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) :=
    hθ.comp hφ.continuousOn (Set.mapsTo_image _ _)
  have h2 : Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)
  exact ((h1.mul h2.continuousOn).integrableOn_compact hE).mono_set subset_closure

theorem integrableOn_char (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have h2 : Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)
  exact (h2.continuousOn.integrableOn_compact hE).mono_set subset_closure

theorem inner_eq (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (z : ℂ) (t : {r : ℝ // 0 < r}) :
    ∫ u in normOneFundamentalDomain k, ∑' ξ : kˣ, ∑' l : Projectivization k (ι → k),
        Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ∂normOneMeasure k =
      (thetaCFun w F ω (t : ℝ) - thetaCConst F ω) *
        (((t : ℝ) : ℂ) ^ (z + (archExponent w ω : ℂ) * Complex.I)) := by
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 t.2.ne'
  have hpt : ∀ u : normOneSubgroup k, ∑' ξ : kˣ, ∑' l : Projectivization k (ι → k),
      Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) =
      (((t : ℝ) : ℂ) ^ (z + (archExponent w ω : ℂ) * Complex.I)) *
        (thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) *
            (ω.toIdele (u : IdeleGroup k) : ℂ) - F 0 * (ω.toIdele (u : IdeleGroup k) : ℂ)) := by
    intro u
    set x : IdeleGroup k := moduleSection w t * (u : IdeleGroup k) with hx
    have hmod : (ideleModule k x : ℝ) = t := by
      have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
      rw [hx, map_mul, ideleModule_moduleSection, hu1, mul_one]
    have e : ∀ ξ : kˣ, diagonal k ξ * moduleSection w t * (u : IdeleGroup k) = diagonal k ξ * x :=
      fun ξ ↦ mul_assoc _ _ _
    simp only [e, Gc_diagonal_mul]
    simp only [tsum_mul_right]
    rw [tsum_tsum_eq hF, hmod, hx, map_mul, Circle.coe_mul, archExponent_spec,
      Complex.cpow_add _ _ ht]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_sub (integrableOn_thetaC_mul hF ω _)
    ((integrableOn_char ω).const_mul _), integral_const_mul, thetaCFun, dif_pos t.2]
  simp only [thetaCInt, thetaCConst, volChar]
  ring

theorem integral_tsum_Gc_eq (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    ∫ x, ∑' l : Projectivization k (ι → k), Gc F ω z l x ∂ideleMeasure k =
      mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω)
        (z + (archExponent w ω : ℂ) * Complex.I) := by
  set y := z + (archExponent w ω : ℂ) * Complex.I with hy
  set g : ℝ → ℂ := fun x ↦ (thetaCFun w F ω x - thetaCConst F ω) * (x : ℂ) ^ y with hg
  rw [integral_ideleMeasure_eq_integral_fundamentalDomain w (integrable_tsum_Gc w hF ω hz hz1)]
  have h : (fun t : {r : ℝ // 0 < r} ↦ ∫ u in normOneFundamentalDomain k, ∑' ξ : kˣ,
        ∑' l : Projectivization k (ι → k),
        Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ∂normOneMeasure k) =
      fun t : {r : ℝ // 0 < r} ↦ g (t : ℝ) := by
    funext t
    exact inner_eq w hF ω z t
  rw [h, integral_posRealMeasure g, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx)
  simp only [hg, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem lines_eq_mellin (w : InfinitePlace k) (ω : HeckeCharacter k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Summable (fun l : Projectivization k (ι → k) ↦ ‖lineZeta F ω z (ratV l.rep)‖) ∧
      ∑' l : Projectivization k (ι → k), lineZeta F ω z (ratV l.rep) =
        mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω)
          (z + (archExponent w ω : ℂ) * Complex.I) := by
  haveI := countable_proj (k := k) (ι := ι)
  have hsum := summable_integral_norm_Gc w hF ω hz hz1
  have hsec : ∀ l : Projectivization k (ι → k), lineZeta F ω z (ratV l.rep) =
      ∫ x, Gc F ω z l x ∂ideleMeasure k := fun l ↦ rfl
  refine ⟨Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun c ↦ ?_) hsum, ?_⟩
  · rw [hsec]
    exact norm_integral_le_integral_norm _
  · have hHS := hasSum_integral_of_summable_integral_norm
      (fun c ↦ integrable_Gc hF ω hz1 c) hsum
    simp only [hsec]
    rw [hHS.tsum_eq]
    exact integral_tsum_Gc_eq w hF ω hz hz1

theorem lineZeta_mulVec (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) (A : GL ι 𝔸[k])
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω z ((A : Matrix ι ι 𝔸[k]) *ᵥ v) = lineZeta (ltr A Ψ) ω z v := by
  simp only [lineZeta, ltr, Matrix.mulVec_smul]

theorem mellin_eq_zero_of_isEmpty [IsEmpty ι] (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) :
    mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω) s = 0 := by
  have hθ : ∀ h : GL ι 𝔸[k], thetaC F h = F 0 := by
    intro h
    rw [thetaC, tsum_eq_single (0 : ι → k) fun ξ hξ ↦ (hξ (Subsingleton.elim _ _)).elim]
    congr 1
    exact Subsingleton.elim _ _
  rw [mellin]
  have h0 : ∫ t in Set.Ioi (0 : ℝ), ((t : ℂ) ^ (s - 1)) •
      (thetaCFun w F ω t - thetaCConst F ω) = ∫ t in Set.Ioi (0 : ℝ), (0 : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [thetaCFun, dif_pos hx', thetaCInt, hθ, thetaCConst, volChar]
    rw [integral_const_mul, sub_self, smul_zero]
  rw [h0]
  simp

end Unfold

theorem epstein_eq_mellin {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) (ω : HeckeCharacter k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re)
    (m : GL ι 𝔸[k]) :
    Summable (fun l : Projectivization k (ι → k) ↦
        ‖lineZeta Ψ ω z (((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV l.rep)‖) ∧
      epstein Ψ ω z m =
        mellin (fun x ↦ thetaCFun w (ltr m⁻¹ Ψ) ω x - thetaCConst (ltr m⁻¹ Ψ) ω)
          (z + (archExponent w ω : ℂ) * Complex.I) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : IsEmpty (Projectivization k (ι → k)) :=
      ⟨fun l ↦ l.rep_nonzero (Subsingleton.elim _ _)⟩
    rw [mellin_eq_zero_of_isEmpty, epstein, tsum_empty]
    exact ⟨Summable.of_finite, rfl⟩
  · have hz1 : 1 < z.re := by
      have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
      linarith
    have h := lines_eq_mellin w ω (GlobalTheory.T.linearChange_mem_schwartzBruhatPi hΨ m⁻¹) hz hz1
    simp only [epstein, lineZeta_mulVec]
    exact h

end GlobalTheory.CompanionTheory.EpsteinUnfold.Hd
end

section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EpsteinMain.Hd

open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
  GroundTheory.Automorphic.GodementSection IdeleGroup PositivityTheory.RgEis Set Asymptotics

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def detMod (A : GL ι 𝔸[k]) : ℝ :=
  (ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ)

theorem detMod_pos (A : GL ι 𝔸[k]) : 0 < detMod A := (ideleModule k _).2

theorem detMod_inv (A : GL ι 𝔸[k]) : detMod A⁻¹ = (detMod A)⁻¹ := by
  simp [detMod, map_inv]

theorem det_tInv (A : GL ι 𝔸[k]) :
    Matrix.GeneralLinearGroup.det (tInv A) = (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  rw [← map_inv]
  ext1
  simp [tInv, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem detMod_tInv (A : GL ι 𝔸[k]) : detMod (tInv A) = (detMod A)⁻¹ := by
  simp [detMod, det_tInv, map_inv]

theorem tInv_tInv (A : GL ι 𝔸[k]) : tInv (tInv A) = A := by
  ext1
  have h : (((tInv A)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = (A : Matrix ι ι 𝔸[k])ᵀ := rfl
  show (((tInv A)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])ᵀ = A
  rw [h, Matrix.transpose_transpose]

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : GL ι 𝔸[k] → IdeleGroup k) :=
  Continuous.units_map (Matrix.detMonoidHom : Matrix ι ι 𝔸[k] →* 𝔸[k])
    (show Continuous fun A : Matrix ι ι 𝔸[k] ↦ A.det from continuous_id.matrix_det)

theorem continuous_detMod : Continuous (detMod : GL ι 𝔸[k] → ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp continuous_det)

theorem continuous_tInv : Continuous (tInv : GL ι 𝔸[k] → GL ι 𝔸[k]) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · have h : Continuous fun A : GL ι 𝔸[k] ↦ (A : Matrix ι ι 𝔸[k])ᵀ :=
      Units.continuous_val.matrix_transpose
    exact h

theorem thetaCFun_of_pos (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    {x : ℝ} (hx : 0 < x) : thetaCFun w F ω x = thetaCInt w F ω ⟨x, hx⟩ := dif_pos hx

theorem thetaCFun_smul (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) : thetaCFun w (c • F) ω = c • thetaCFun w F ω := by
  funext x
  by_cases hx : 0 < x
  · simp only [Pi.smul_apply, smul_eq_mul, thetaCFun_of_pos w _ ω hx]
    exact GlobalTheory.CompanionTheory.He2M1.thetaCInt_smul w c F ω _
  · simp [thetaCFun, hx]

theorem thetaCFun_neg (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCFun w (fun x ↦ F (-x)) ω = thetaCFun w F ω := by
  funext x
  unfold thetaCFun
  rw [GlobalTheory.CompanionTheory.AdelicThetaSeries.thetaCInt_neg w F ω]

theorem thetaCConst_smul (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (c • F) ω = c * thetaCConst F ω := by
  simp [thetaCConst, mul_assoc]

theorem thetaCConst_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (ltr A F) ω = thetaCConst F ω := by
  simp [thetaCConst, ltr]

theorem thetaCConst_neg (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (fun x ↦ F (-x)) ω = thetaCConst F ω := by
  simp [thetaCConst]

theorem ltr_one (F : (ι → 𝔸[k]) → ℂ) : ltr (1 : GL ι 𝔸[k]) F = F := by
  funext x
  simp [ltr]

theorem ltr_neg (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    ltr A (fun x ↦ F (-x)) = fun x ↦ ltr A F (-x) := by
  funext x
  simp [ltr, Matrix.mulVec_neg]

theorem fourier_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    adelicFourierPi k (ltr A F) =
      (((detMod A : ℝ) : ℂ)⁻¹) • ltr (tInv A) (adelicFourierPi k F) :=
  GlobalTheory.CompanionTheory.LtrFourier.Hd.adelicFourierPi_ltr A F

theorem thetaCFun_decay (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ A ∈ C, ∀ x : ℝ, 1 ≤ x →
      ‖thetaCFun w (ltr A Ψ) ω x - thetaCConst (ltr A Ψ) ω‖ ≤ M * x ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge r
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.AdelicThetaSeries.exists_norm_thetaCInt_sub_le w hΨ ω hC N
  refine ⟨max M 0, le_max_right _ _, fun A hA x hx ↦ ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h := hM A hA ⟨x, hx0⟩ hx
  rw [← thetaCFun_of_pos w _ ω hx0] at h
  have hpow : (x ^ N)⁻¹ ≤ x ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hp0 : 0 ≤ (x ^ N)⁻¹ := by positivity
  calc _ ≤ (x ^ N)⁻¹ * M := h
    _ ≤ (x ^ N)⁻¹ * max M 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hp0
    _ ≤ x ^ (-r) * max M 0 := mul_le_mul_of_nonneg_right hpow (le_max_right _ _)
    _ = _ := mul_comm _ _

theorem isBigO_thetaCFun_sub (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (r : ℝ) :
    (fun x ↦ thetaCFun w F ω x - thetaCConst F ω) =O[atTop] (· ^ r) := by
  obtain ⟨M, -, hM⟩ := thetaCFun_decay w hF ω (isCompact_singleton (x := (1 : GL ι 𝔸[k]))) (-r)
  refine IsBigO.of_bound M ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := hM 1 rfl x hx
  rw [ltr_one, neg_neg] at h
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) r)]

theorem continuousOn_thetaCFun_ltr (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    ContinuousOn (fun q : GL ι 𝔸[k] × ℝ ↦ thetaCFun w (ltr q.1 Ψ) ω q.2) (univ ×ˢ Ioi 0) := by
  have h := GlobalTheory.CompanionTheory.EpsteinThetaC.continuous_thetaCInt_ltr w hΨ ω
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous fun q : ↥(univ ×ˢ Ioi (0 : ℝ) : Set (GL ι 𝔸[k] × ℝ)) ↦
      ((⟨q.1.2, q.2.2⟩ : {r : ℝ // 0 < r}), q.1.1) :=
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  refine (h.comp hc).congr fun q ↦ ?_
  simp only [restrict, Function.comp]
  exact (thetaCFun_of_pos w _ ω q.2.2).symm

theorem continuousOn_thetaCFun (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    ContinuousOn (thetaCFun w F ω) (Ioi 0) := by
  have h := continuousOn_thetaCFun_ltr w hF ω
  have h2 := h.comp (f := fun x : ℝ ↦ ((1 : GL ι 𝔸[k]), x)) (s := Ioi 0) (by fun_prop)
    (fun x hx ↦ ⟨mem_univ _, hx⟩)
  simpa [Function.comp_def, ltr_one] using h2

theorem thetaCFun_one_div (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) {ω : HeckeCharacter k} (hω : ω * ω = 1) (x : ℝ)
    (hx : x ∈ Ioi (0 : ℝ)) :
    thetaCFun w F ω (1 / x) =
      ((1 : ℂ) * ((x ^ (Fintype.card ι : ℝ) : ℝ) : ℂ)) • thetaCFun w (adelicFourierPi k F) ω x := by
  have hx0 : (0 : ℝ) < x := hx
  have h := GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd.thetaCInt_inv w hF ω ⟨x, hx0⟩
  rw [← eq_inv_of_mul_eq_one_left hω] at h
  rw [thetaCFun_of_pos w _ ω (one_div_pos.2 hx0), thetaCFun_of_pos w _ ω hx0, Real.rpow_natCast]
  have e : (⟨1 / x, one_div_pos.2 hx0⟩ : {r : ℝ // 0 < r}) = (⟨x, hx0⟩ : {r : ℝ // 0 < r})⁻¹ := by
    ext
    simp
  rw [e, h]
  simp

noncomputable def pair [Nonempty ι] (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) {ω : HeckeCharacter k} (hω : ω * ω = 1) : WeakFEPair ℂ where
  f := thetaCFun w F ω
  g := thetaCFun w (adelicFourierPi k F) ω
  k := Fintype.card ι
  ε := 1
  f₀ := thetaCConst F ω
  g₀ := thetaCConst (adelicFourierPi k F) ω
  hf_int := (continuousOn_thetaCFun w hF ω).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_thetaCFun w (adelicFourierPi_mem_schwartzBruhatPi hF) ω).locallyIntegrableOn
    measurableSet_Ioi
  hk := by exact_mod_cast Fintype.card_pos
  hε := one_ne_zero
  h_feq := thetaCFun_one_div w hF hω
  hf_top := isBigO_thetaCFun_sub w hF ω
  hg_top := isBigO_thetaCFun_sub w (adelicFourierPi_mem_schwartzBruhatPi hF) ω

noncomputable def entireForm (P : WeakFEPair ℂ) (z : ℂ) : ℂ :=
  z * (z - P.k) * P.Λ₀ z - (z - P.k) * P.f₀ + z * P.ε * P.g₀

theorem entireForm_eq (P : WeakFEPair ℂ) {z : ℂ} (h0 : z ≠ 0) (hk : z ≠ P.k) :
    entireForm P z = z * (z - P.k) * P.Λ z := by
  have h1 : z - P.k ≠ 0 := sub_ne_zero.2 hk
  have h2 : (P.k : ℂ) - z ≠ 0 := sub_ne_zero.2 hk.symm
  simp only [entireForm, WeakFEPair.Λ, smul_eq_mul]
  field_simp
  ring

theorem differentiable_entireForm (P : WeakFEPair ℂ) : Differentiable ℂ (entireForm P) := by
  unfold entireForm
  have := P.differentiable_Λ₀
  fun_prop

theorem thetaCFun_fourier_ltr (w : InfinitePlace k) (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) :
    thetaCFun w (adelicFourierPi k (ltr A F)) ω =
      (((detMod A : ℝ) : ℂ)⁻¹) • thetaCFun w (ltr (tInv A) (adelicFourierPi k F)) ω := by
  rw [fourier_ltr, thetaCFun_smul]

theorem thetaCConst_fourier_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (adelicFourierPi k (ltr A F)) ω =
      ((detMod A : ℝ) : ℂ)⁻¹ * thetaCConst (adelicFourierPi k F) ω := by
  rw [fourier_ltr, thetaCConst_smul, thetaCConst_ltr]

noncomputable def pairAt [Nonempty ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) {ω : HeckeCharacter k} (hω : ω * ω = 1) (A : GL ι 𝔸[k]) :
    WeakFEPair ℂ :=
  pair w (GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem hΨ A) hω

section pairAt

variable [Nonempty ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
  (hΨ : Ψ ∈ schwartzBruhatPi k ι) {ω : HeckeCharacter k} (hω : ω * ω = 1)

theorem pairAt_bound {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ A ∈ C, ∀ x : ℝ, 1 ≤ x →
      ‖(pairAt w hΨ hω A).f x - (pairAt w hΨ hω A).f₀‖ ≤ M * x ^ (-r) ∧
      ‖(pairAt w hΨ hω A).g x - (pairAt w hΨ hω A).g₀‖ ≤ M * x ^ (-r) := by
  obtain ⟨M₁, hM₁, h₁⟩ := thetaCFun_decay w hΨ ω hC r
  obtain ⟨M₂, hM₂, h₂⟩ := thetaCFun_decay w (adelicFourierPi_mem_schwartzBruhatPi hΨ) ω
    (hC.image continuous_tInv) r
  have hcont : ContinuousOn (fun A : GL ι 𝔸[k] ↦ (detMod A)⁻¹) C :=
    (continuous_detMod.inv₀ fun A ↦ (detMod_pos A).ne').continuousOn
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont
  refine ⟨max M₁ (max B 0 * M₂), le_max_of_le_left hM₁, fun A hA x hx ↦ ⟨?_, ?_⟩⟩
  · have hp : 0 ≤ x ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hx) _
    exact (h₁ A hA x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hp : 0 ≤ x ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hx) _
    have e : (pairAt w hΨ hω A).g x - (pairAt w hΨ hω A).g₀ =
        ((detMod A : ℝ) : ℂ)⁻¹ * (thetaCFun w (ltr (tInv A) (adelicFourierPi k Ψ)) ω x -
          thetaCConst (ltr (tInv A) (adelicFourierPi k Ψ)) ω) := by
      show thetaCFun w (adelicFourierPi k (ltr A Ψ)) ω x -
        thetaCConst (adelicFourierPi k (ltr A Ψ)) ω = _
      rw [thetaCFun_fourier_ltr, thetaCConst_fourier_ltr, thetaCConst_ltr, Pi.smul_apply,
        smul_eq_mul, mul_sub]
    have hn : ‖((detMod A : ℝ) : ℂ)⁻¹‖ ≤ max B 0 := by
      have := hB A hA
      simp only [Real.norm_eq_abs, abs_inv] at this
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
      exact this.trans (le_max_left _ _)
    rw [e, norm_mul]
    calc _ ≤ max B 0 * (M₂ * x ^ (-r)) :=
          mul_le_mul hn (h₂ _ ⟨A, hA, rfl⟩ x hx) (norm_nonneg _) (le_max_right _ _)
      _ = (max B 0 * M₂) * x ^ (-r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp

theorem continuous_pairAt_f₀ : Continuous fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).f₀ := by
  have h : (fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).f₀) = fun _ ↦ thetaCConst Ψ ω := by
    funext A
    exact thetaCConst_ltr A Ψ ω
  rw [h]
  exact continuous_const

theorem continuous_inv_detMod : Continuous fun A : GL ι 𝔸[k] ↦ ((detMod A : ℝ) : ℂ)⁻¹ :=
  (Complex.continuous_ofReal.comp continuous_detMod).inv₀ fun A ↦
    Complex.ofReal_ne_zero.2 (detMod_pos A).ne'

theorem continuous_pairAt_g₀ : Continuous fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).g₀ := by
  have h : (fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).g₀) = fun A ↦
      ((detMod A : ℝ) : ℂ)⁻¹ * thetaCConst (adelicFourierPi k Ψ) ω := by
    funext A
    exact thetaCConst_fourier_ltr A Ψ ω
  rw [h]
  exact continuous_inv_detMod.mul continuous_const

theorem continuous_pairAt_Λ₀ : Continuous fun q : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω q.2).Λ₀ q.1 := by
  refine GlobalTheory.CompanionTheory.EisRk1Cont.weakFEPair_continuous_Λ₀ (pairAt w hΨ hω) (Fintype.card ι)
    (fun _ ↦ rfl) 1 (fun _ ↦ rfl) ?_ ?_ (continuous_pairAt_f₀ w hΨ hω)
    (continuous_pairAt_g₀ w hΨ hω) ?_
  · exact continuousOn_thetaCFun_ltr w hΨ ω
  · have h1 := continuousOn_thetaCFun_ltr w (adelicFourierPi_mem_schwartzBruhatPi hΨ) ω
    have h2 := h1.comp (f := fun q : GL ι 𝔸[k] × ℝ ↦ (tInv q.1, q.2)) (s := univ ×ˢ Ioi 0)
      ((continuous_tInv.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨mem_univ _, hq.2⟩)
    have h3 : Continuous fun q : GL ι 𝔸[k] × ℝ ↦ ((detMod q.1 : ℝ) : ℂ)⁻¹ :=
      continuous_inv_detMod.comp continuous_fst
    refine (h3.continuousOn.mul h2).congr fun q _ ↦ ?_
    show thetaCFun w (adelicFourierPi k (ltr q.1 Ψ)) ω q.2 = _
    rw [thetaCFun_fourier_ltr]
    rfl
  · intro p₀ r
    obtain ⟨C, hC, hp⟩ := exists_compact_mem_nhds p₀
    obtain ⟨M, -, hM⟩ := pairAt_bound w hΨ hω hC r
    exact ⟨C, hp, M, hM⟩

theorem pairAt_k (A : GL ι 𝔸[k]) : (pairAt w hΨ hω A).k = (Fintype.card ι : ℝ) := rfl

theorem pairAt_ε (A : GL ι 𝔸[k]) : (pairAt w hΨ hω A).ε = 1 := rfl

theorem continuous_entireForm_inv :
    Continuous fun y : ℂ × GL ι 𝔸[k] ↦ entireForm (pairAt w hΨ hω y.2⁻¹) y.1 := by
  have hinv : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ y.2⁻¹ := continuous_inv.comp continuous_snd
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ ((y.1, y.2⁻¹) : ℂ × GL ι 𝔸[k]) :=
    continuous_fst.prodMk hinv
  have hΛ : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).Λ₀ y.1 := by
    have h := (continuous_pairAt_Λ₀ w hΨ hω).comp hc
    simpa only [Function.comp_def] using h
  have hf : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).f₀ := by
    have h := (continuous_pairAt_f₀ w hΨ hω).comp hinv
    simpa only [Function.comp_def] using h
  have hg : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).g₀ := by
    have h := (continuous_pairAt_g₀ w hΨ hω).comp hinv
    simpa only [Function.comp_def] using h
  have hz : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ y.1 - (((Fintype.card ι : ℝ)) : ℂ) :=
    continuous_fst.sub continuous_const
  simp only [entireForm, pairAt_k, pairAt_ε]
  exact (((continuous_fst.mul hz).mul hΛ).sub (hz.mul hf)).add
    ((continuous_fst.mul continuous_const).mul hg)

theorem isEpCont : IsEpCont Ψ ω fun z m ↦ entireForm (pairAt w hΨ hω m⁻¹) z where
  entire m := differentiable_entireForm _
  cont := continuous_entireForm_inv w hΨ hω
  eq := by
    intro z hz m
    have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [Complex.zero_re] at hz
      linarith
    have hzk : z ≠ (((pairAt w hΨ hω m⁻¹).k : ℝ) : ℂ) := by
      intro h
      have h2 : z.re = (Fintype.card ι : ℝ) := by
        rw [h]
        exact Complex.ofReal_re _
      linarith
    have hm := ((pairAt w hΨ hω m⁻¹).hasMellin (s := z) hz).2
    have he := (GlobalTheory.CompanionTheory.EpsteinUnfold.Hd.epstein_eq_mellin w ω hΨ hz m).2
    rw [GlobalTheory.CompanionTheory.EisRk1.archExponent_eq_zero_of_mul_self w hω] at he
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at he
    show entireForm (pairAt w hΨ hω m⁻¹) z = _
    rw [entireForm_eq _ hz0 hzk, he]
    have hk : (((pairAt w hΨ hω m⁻¹).k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
      show (((Fintype.card ι : ℝ)) : ℂ) = _
      simp
    rw [hk, ← hm]
    rfl
  strip := by
    intro a b C hC
    have hC' : IsCompact ((fun m : GL ι 𝔸[k] ↦ m⁻¹) '' C) := hC.image continuous_inv
    set N : ℝ := (Fintype.card ι : ℝ) with hNdef
    have hN : 0 ≤ N := Nat.cast_nonneg _
    obtain ⟨M, hM0, hM⟩ := pairAt_bound w hΨ hω hC' (|a| + |b| + N + 1)
    obtain ⟨B₁, hB₁⟩ := hC'.exists_bound_of_continuousOn
      (continuous_pairAt_f₀ w hΨ hω).continuousOn
    obtain ⟨B₂, hB₂⟩ := hC'.exists_bound_of_continuousOn
      (continuous_pairAt_g₀ w hΨ hω).continuousOn
    set B : ℝ := max 0 (max B₁ B₂) with hBdef
    have hB0 : 0 ≤ B := le_max_left _ _
    refine ⟨(N + 1) * (2 * M) + (N + 2) * B, fun z hza hzb m hm ↦ ?_⟩
    have hA : m⁻¹ ∈ (fun m : GL ι 𝔸[k] ↦ m⁻¹) '' C := ⟨m, hm, rfl⟩
    set P := pairAt w hΨ hω m⁻¹ with hP
    have hPk : P.k = N := rfl
    have hPε : P.ε = 1 := rfl
    have ha := neg_abs_le a
    have hb := le_abs_self b
    have habs := abs_nonneg a
    have habs' := abs_nonneg b
    have h1 : 1 ≤ (|a| + |b| + N + 1) - z.re := by linarith
    have h2 : 1 ≤ (|a| + |b| + N + 1) - (P.k - z.re) := by rw [hPk]; linarith
    have hΛ := GlobalTheory.CompanionTheory.EisRk1.weakFEPair_norm_Λ₀_le P (r := |a| + |b| + N + 1) (M := M)
      (fun x hx ↦ (hM _ hA x hx).1) (fun x hx ↦ (hM _ hA x hx).2) z (by linarith) (by linarith)
    have hΛ' : ‖P.Λ₀ z‖ ≤ 2 * M := by
      rw [hPε, norm_one, one_mul] at hΛ
      have e1 := div_le_self hM0 h1
      have e2 := div_le_self hM0 h2
      linarith
    have hf₀ : ‖P.f₀‖ ≤ B := (hB₁ _ hA).trans ((le_max_left _ _).trans (le_max_right _ _))
    have hg₀ : ‖P.g₀‖ ≤ B := (hB₂ _ hA).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hzn : ‖z - ((N : ℝ) : ℂ)‖ ≤ ‖z‖ + N := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hN]
    show ‖entireForm P z‖ ≤ _
    have hnorm : ‖entireForm P z‖ ≤ ‖z‖ * (‖z‖ + N) * (2 * M) + (‖z‖ + N) * B + ‖z‖ * B := by
      have e : entireForm P z = z * (z - ((N : ℝ) : ℂ)) * P.Λ₀ z - (z - ((N : ℝ) : ℂ)) * P.f₀ +
          z * P.g₀ := by
        simp only [entireForm, hPk, hPε, mul_one]
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)) hΛ' (norm_nonneg _)
          (by positivity)
      · rw [norm_mul]
        exact mul_le_mul hzn hf₀ (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hg₀ (norm_nonneg _)
    refine hnorm.trans ?_
    set s : ℝ := ‖z‖ with hs
    have hs0 : 0 ≤ s := norm_nonneg _
    have hL : 0 ≤ 2 * M := by positivity
    have t1 : s * (s + N) * (2 * M) ≤ (N + 1) * (2 * M) * (1 + s) ^ 2 := by
      have : s * (s + N) ≤ (N + 1) * (1 + s) ^ 2 := by nlinarith [mul_nonneg hN hs0, mul_nonneg hs0 hs0, mul_nonneg hN (mul_nonneg hs0 hs0)]
      nlinarith
    have t2 : (s + N) * B + s * B ≤ (N + 2) * B * (1 + s) ^ 2 := by
      have : (s + N) + s ≤ (N + 2) * (1 + s) ^ 2 := by nlinarith [mul_nonneg hN hs0, mul_nonneg hs0 hs0, mul_nonneg hN (mul_nonneg hs0 hs0)]
      nlinarith
    nlinarith

theorem entireForm_fe (A : GL ι 𝔸[k]) (z : ℂ) :
    entireForm (pairAt w hΨ hω A) z = ((detMod A : ℝ) : ℂ)⁻¹ *
      entireForm (pairAt w (adelicFourierPi_mem_schwartzBruhatPi hΨ) hω (tInv A))
        ((Fintype.card ι : ℂ) - z) := by
  have hΨ' := adelicFourierPi_mem_schwartzBruhatPi hΨ
  set P := pairAt w hΨ hω A with hP
  set Q := pairAt w hΨ' hω (tInv A) with hQ
  set d : ℂ := ((detMod A : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.2 (detMod_pos A).ne'
  have hdinv : (((detMod (tInv A) : ℝ) : ℂ)⁻¹) = d := by
    rw [detMod_tInv, Complex.ofReal_inv, inv_inv]
  have hneg : ltr A (adelicFourierPi k (adelicFourierPi k Ψ)) = fun x ↦ ltr A Ψ (-x) := by
    rw [adelicFourierPi_adelicFourierPi hΨ, ltr_neg]
  have hQg : Q.g = d • P.f := by
    show thetaCFun w (adelicFourierPi k (ltr (tInv A) (adelicFourierPi k Ψ))) ω =
      d • thetaCFun w (ltr A Ψ) ω
    rw [thetaCFun_fourier_ltr, hdinv, tInv_tInv, hneg, thetaCFun_neg]
  have hQg₀ : Q.g₀ = d * P.f₀ := by
    show thetaCConst (adelicFourierPi k (ltr (tInv A) (adelicFourierPi k Ψ))) ω =
      d * thetaCConst (ltr A Ψ) ω
    rw [fourier_ltr, hdinv, tInv_tInv, hneg, thetaCConst_smul, thetaCConst_neg]
  have hPg : P.g = d⁻¹ • Q.f := by
    show thetaCFun w (adelicFourierPi k (ltr A Ψ)) ω =
      d⁻¹ • thetaCFun w (ltr (tInv A) (adelicFourierPi k Ψ)) ω
    rw [thetaCFun_fourier_ltr]
  have hPg₀ : P.g₀ = d⁻¹ * Q.f₀ := by
    show thetaCConst (adelicFourierPi k (ltr A Ψ)) ω =
      d⁻¹ * thetaCConst (ltr (tInv A) (adelicFourierPi k Ψ)) ω
    rw [fourier_ltr, thetaCConst_smul]
  have hPf : P.f = d⁻¹ • Q.g := by
    rw [hQg, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hPf₀ : P.f₀ = d⁻¹ * Q.g₀ := by
    rw [hQg₀, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  have key : P.Λ₀ = d⁻¹ • Q.symm.Λ₀ :=
    GlobalTheory.CompanionTheory.EisRankOne.weakFEPair_Λ₀_of_smul Q.symm P d⁻¹ hPf hPg rfl
      (show (1 : ℂ) = (1 : ℂ)⁻¹ by simp) hPf₀ hPg₀
  have hfe := Q.functional_equation₀ z
  have hQk : ((Q.k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
    show (((Fintype.card ι : ℝ)) : ℂ) = _
    simp
  have hPk : ((P.k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := hQk
  have hQε : Q.ε = 1 := rfl
  have hPε : P.ε = 1 := rfl
  rw [hQk, hQε, one_smul] at hfe
  simp only [entireForm, hQk, hPk, hQε, hPε, hfe, key, Pi.smul_apply, smul_eq_mul, hPf₀, hPg₀]
  ring

end pairAt

theorem epMain_of_epConv : EpConv → EpMain := by
  intro _ k _ _
  obtain ⟨V, hV, hvol⟩ :=
    (GlobalTheory.CompanionTheory.EpsteinVol.volChar_one_eq : ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ))
  obtain ⟨w⟩ : Nonempty (InfinitePlace k) := inferInstance
  refine ⟨V, hV, fun ι _ _ _ Ψ ω hΨ hω ↦ ?_⟩
  have hΨ' := adelicFourierPi_mem_schwartzBruhatPi hΨ
  refine ⟨fun z m ↦ entireForm (pairAt w hΨ hω m⁻¹) z,
    fun z m ↦ entireForm (pairAt w hΨ' hω m⁻¹) z, isEpCont w hΨ hω, isEpCont w hΨ' hω, ?_, ?_⟩
  · intro z m
    have h := entireForm_fe w hΨ hω m⁻¹ z
    have e : modPow (Matrix.GeneralLinearGroup.det m) 1 = ((detMod m : ℝ) : ℂ) := by
      simp [modPow, detMod]
    rw [map_inv, detMod_inv, Complex.ofReal_inv, inv_inv] at h
    rw [e]
    exact h
  · rintro rfl m
    have hk : ∀ A : GL ι 𝔸[k], (((pairAt w hΨ hω A).k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
      intro A
      show (((Fintype.card ι : ℝ)) : ℂ) = _
      simp
    have hε : ∀ A : GL ι 𝔸[k], (pairAt w hΨ hω A).ε = 1 := fun _ ↦ rfl
    have hf₀ : (pairAt w hΨ hω m⁻¹).f₀ = Ψ 0 * V := by
      show thetaCConst (ltr m⁻¹ Ψ) 1 = _
      rw [thetaCConst_ltr, thetaCConst, hvol]
    have hg₀ : (pairAt w hΨ hω m⁻¹).g₀ = ((detMod m : ℝ) : ℂ) * (adelicFourierPi k Ψ 0 * V) := by
      show thetaCConst (adelicFourierPi k (ltr m⁻¹ Ψ)) 1 = _
      rw [thetaCConst_fourier_ltr, detMod_inv, Complex.ofReal_inv, inv_inv, thetaCConst, hvol]
    have e : modPow (Matrix.GeneralLinearGroup.det m) 1 = ((detMod m : ℝ) : ℂ) := by
      simp [modPow, detMod]
    refine ⟨?_, ?_⟩
    · simp only [entireForm, hk, hε, hf₀, hg₀]
      ring
    · simp only [entireForm, hk, hε, hf₀, hg₀, e]
      ring

end GlobalTheory.CompanionTheory.EpsteinMain.Hd
end

section
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisSo.Hd

theorem blg_of_dict : Dict → BLg := by
  intro hD F E _ _ _ _ _ σ χ c hσ _ _ _
  obtain ⟨-, -, -, -, h5⟩ := hD F E
  have key : ∀ x : (IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, (adCM σ χ).lg x =
      Real.log (GlobalTheory.Doubling.absE F E x : ℝ) := fun x => by
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = _
    rw [h5]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have e : Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x) =
        GroundTheory.Global.ideleEmbedding F E x := by
      apply Units.ext
      exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x)) : ℝ) =
      2 * Real.log (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ)
    rw [e, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F),
      GroundTheory.Global.ideleNorm_ideleEmbedding, hσ.2.2.1, map_pow]
    have : (((GroundTheory.Global.IdeleGroup.ideleModule F x) ^ 2 : {r : ℝ // 0 < r}) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ) ^ 2 := rfl
    rw [this, Real.log_pow]
    norm_num
  · rw [key, key]
    have e : Units.map (adCM σ χ).σ.toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
      apply Units.ext
      rfl
    rw [e, GlobalTheory.Doubling.absE_conjUnit]
end GlobalTheory.CompanionTheory.RgEisSo.Hd
end

section
namespace PositivityTheory.RgEis.So

theorem sgOne_hd : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := fun sl _ sc sg dict _ cg gt bl el pl mg =>
  have jt := GlobalTheory.CompanionTheory.EisSo.jtop
  have jc := GlobalTheory.CompanionTheory.RgEisSo.jcpt sg gt jt
  have ji := GlobalTheory.CompanionTheory.RgEisSo.JIwaAd.jiwa sg
  have jch := GlobalTheory.CompanionTheory.EisSo.jCh sg bl jt
  sgOne_of_parts
    (GlobalTheory.CompanionTheory.SgOneBase.baseCM cg GlobalTheory.CompanionTheory.RgEisFix.bFix GlobalTheory.CompanionTheory.EisBrat.brat GlobalTheory.CompanionTheory.RgEisBInt.bInt GlobalTheory.CompanionTheory.RgEisSo.bInf (GlobalTheory.CompanionTheory.RgEisSo.Hd.blg_of_dict dict) GlobalTheory.CompanionTheory.CMDelta.bDel)
    GlobalTheory.CompanionTheory.RgEis.Cover.jEx jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat (GlobalTheory.CompanionTheory.EisSec.jSec_of_top jt) jch
    (GlobalTheory.CompanionTheory.EisJMir.jmir sg gt bl el pl jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat jch) (GlobalTheory.CompanionTheory.RgDescendWall.descend2 sl) (GlobalTheory.CompanionTheory.RgEisTwist.twist sl) sc cg gt pl mg

end PositivityTheory.RgEis.So
end

section
noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := GlobalTheory.T.identity_tube_holds
theorem tubeChain : TubeChain := GlobalTheory.T.tube_chain_holds
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
theorem htLip : HtLip := GlobalTheory.T.height_lipschitz_holds
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
theorem wallLaw_of : SecLaw → WallLaw := GlobalTheory.T.wall_law_of_section_law
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := GlobalTheory.T.gallery_of_tubes_and_crossing
theorem transfer_of : SecLaw → WallLaw → Transfer := GlobalTheory.T.transfer_of_section_and_wall_laws
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
theorem grpTop : GrpTop := GlobalTheory.T.general_linear_topological_group
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := GlobalTheory.T.levi_quotient_of_block_det
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := GlobalTheory.T.convergence_group_of_block_det
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
theorem stdGood : StdGood := GlobalTheory.T.standard_section_good
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := GlobalTheory.T.constant_multiplier_good
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of GlobalTheory.T.eisenstein_half_holds
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
end
end
