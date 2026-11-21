import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAreaFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeBallFinite
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFsLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeHyperplaneNull
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeRadialIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSlabBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadBlockGaussTail
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadPlaneJac
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjChowNonzero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjDegreeChow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjSecDomain
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecDegreeGe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecDegreeLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecFiniteUnit
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecRankSpecialize
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussMoment
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartChoice
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFinite
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFirstGroupDvd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartFirstGroupPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartKernel
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLength
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartMaxIdeals
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartNorm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartResidueDegree
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PComponentOfIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PDehomogOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PEmultiplicityOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthFiniteAlgebra
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLinearFormPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLocalMultOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLocalizationPrimeDVR
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMapDvdDescent
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormDvd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormEmbeddings
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormEval
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormOfDividedForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PPrimeMapFractionRing
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstMemIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstNe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPartition
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPiece
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaMultiplicity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCauchyBinetMinors
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PComplexJacobian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConePolar
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeScaling
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConePolar
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaneSliceMass
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PContinuousRootHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionPolynomial
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StContinuousRootHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionCoordinateEquation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffShape
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreSectionsCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteCoverPuncturedPolydisc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntSymm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFrameJacobianSum
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFunctionFieldDegree
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGeneralProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericPrimitive
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphJacContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGreenFromLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHessCCompPluri
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphProjectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHess
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionHyperplaneAvoid
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionDegreeSum
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPointSliceMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POneComponentGeneralPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPointSliceMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolySublevel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPowerUnitCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionCoordinateEquation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedCoverCycles
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegConeLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRemovableHyperplane
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionPolynomial
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetComass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetLogNormDens
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutDecay
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceExhaustion
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLelongError
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMatricesOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarSlabMeasure
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyProjectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietySlabMeasure
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroSetOpenMass

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

theorem AreaLinear.sqrt_det_adjoint_comp_eq_normDet {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)

theorem AreaLinear.proof : AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem gramVol_const_zero {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  unfold gramVol
  have hw : (Fin.cons 0 (fun _ => 0) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have h0 : (Matrix.of fun (_ _ : Fin (e + 1)) => (0 : ℂ)).det = 0 := Matrix.det_zero
  simp [hw, h0]

theorem succ_le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem ConeSheetGram.proof (hL : ConeSheetGramLintegral.Statement) : ConeSheetGram.Statement := by
  intro n e h J ℓ A f hJ hdim hℓ hA hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (succ_le_of_ringKrullDim_quotient J hdim)
  rw [mul_setIntegral_eq_of_lintegral (ν := volume) (fun y => IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)
    (fun y x => WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))
    (fun y x t => ‖t‖ ^ (2 * e) *
      gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)
    (fun y x t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ y))
    (fun y x => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => hL n e h J ℓ A F hJ hdim hℓ hA hF) hf]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  unfold sheetSum
  refine finsum_congr fun x => finsum_congr fun _ => ?_
  unfold sheetThrough
  split_ifs with hs
  · rfl
  · simp [gramVol_const_zero]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem coneIntegral_space_one (e : ℕ) :
    coneIntegral (HermNorm.std (e + 1)) (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e
      (fun _ => 1) = 1 := by
  have hS : {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧
        ∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)),
          eval ((HermNorm.std (e + 1)).pointOf y) q = 0} =
      {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧ ∀ j : Fin (e + 1), e + 1 ≤ (j : ℕ) → y j = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Ideal.mem_bot]
    refine and_congr_right fun _ => ⟨fun _ j hj => absurd j.isLt (by omega), fun _ q hq => ?_⟩
    rw [hq, map_zero]
  obtain ⟨h0, htop⟩ := coordBall_mass (n := e + 1) (m := e + 1) le_rfl
  rw [coneIntegral, hS, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  exact div_self (ENNReal.toReal_ne_zero.mpr ⟨h0.ne', htop.ne⟩)

theorem ConeToProjective.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConePolar.Statement)
    (h₃ : PlaneSliceMass.Statement) : ConeToProjective.Statement := by
  intro n e h J F ℓ g hJ hF hℓ hg hgc
  obtain ⟨κ, hκ⟩ := h₂ e
  have hplane := hκ (e + 1) (HermNorm.std (e + 1)) ⊥ (Pi.single 0 1) (fun _ => 1)
    (isProjPrime_bot_space e) (space_dim (e + 1)) (linForm_single_not_mem_bot 0)
    (fun _ _ _ => rfl) continuousOn_const
  rw [coneIntegral_space_one, linForm_single, bot_sup_eq, h₃ e, mul_one] at hplane
  rw [hκ n h J ℓ g hJ (h₁ ℂ n (e + 1) J F hJ hF) hℓ hg hgc, ← hplane, one_mul]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def ContinuousSectionHolomorphic.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ)
    (O : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin n → ℂ),
    IsAffVariety J k → IsOpen O → ContinuousOn g O → (∀ y ∈ O, g y ∈ zeroLocus J) →
    (∀ y ∈ O, A *ᵥ g y = y) → DifferentiableOn ℂ g O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

noncomputable section

theorem ContinuousSectionHolomorphic.proof (hP : ProjectionCoordinateEquation.Statement)
    (hR : ContinuousRootHolomorphic.Statement) (hE : RiemannExtensionPolynomial.Statement) :
    ContinuousSectionHolomorphic.Statement := by
  intro n k J A O g hJ hO hg hZ hA
  rcases O.eq_empty_or_nonempty with rfl | hne
  · exact differentiableOn_empty
  have hsurj : ∀ y ∈ O, ∃ x ∈ zeroLocus J, A *ᵥ x = y := fun y hy => ⟨g y, hZ y hy, hA y hy⟩
  choose Q D hD0 hQ hQ' using hP n k J A O hJ hO hne hsurj
  have hP0 : (∏ j, D j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hD0 j
  rw [differentiableOn_pi]
  intro j
  have hcont : ContinuousOn (fun y => g y j) O := (continuous_apply j).comp_continuousOn hg
  refine hE k (∏ j, D j) O (fun y => g y j) hP0 hO hcont ?_
  rintro y ⟨hy, hPy⟩
  have hyx : A *ᵥ g y = y := hA y hy
  have hDj : eval y (D j) ≠ 0 := by
    intro h0
    apply hPy
    show eval y (∏ i, D i) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  have hroot : ∀ t ∈ O, eval (Fin.cons (g t j) t : Fin (k + 1) → ℂ) (Q j) = 0 := by
    intro t ht
    have h := hQ j (g t) (hZ t ht)
    rwa [hA t ht] at h
  have hder : eval (Fin.cons (g y j) y : Fin (k + 1) → ℂ) (pderiv 0 (Q j)) ≠ 0 := by
    have h := hQ' j (g y) (hZ y hy) (by rwa [hyx])
    rwa [hyx] at h
  exact (hR k (Q j) O (fun t => g t j) hO hcont hroot y hy hder).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem CutOffLimit.proof (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by
  intro n d J A P hJ hdim hA hP
  obtain ⟨χ, hχs, hχI, hχU, hχ1, hχE, hχM⟩ := hC n d J A P hJ hdim hA hP
  refine ⟨χ, hχs, hχU, fun F G φ hF hG hφ hc => ?_⟩
  have hcont : ∀ f, SmoothNear (zeroSet J) f → ContinuousOn f (zeroSet J) := by
    rintro f ⟨U, -, hU, hf⟩
    exact hf.continuousOn.mono hU
  have hcons : ∀ f, SmoothNear (zeroSet J) f → ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro f hf i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hφ i
  have hmeas : ∀ k, Measurable (χ k) := fun k => (hχs k).continuous.measurable
  refine ⟨hD n (d + 1) J A P χ F (vecCons G φ) hJ hdim hA hP hmeas hχI hχ1 (hcont F hF) (hcons G hG)
    (hM n (d + 1) J A F (vecCons G φ) hJ hdim hA (hcont F hF) (hcons G hG) (Or.inl hc)), ?_⟩
  have h1 := hD n (d + 1) J A P χ G (vecCons F φ) hJ hdim hA hP hmeas hχI hχ1 (hcont G hG) (hcons F hF)
    (hM n (d + 1) J A G (vecCons F φ) hJ hdim hA (hcont G hG) (hcons F hF) (Or.inr ⟨0, by simpa using hc⟩))
  obtain ⟨R, C, hRC⟩ := hB n d J A F G φ hJ hdim hA hF hG hφ hc
  have h0 : Tendsto (fun k => C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (χ k) φ) y) + Real.sqrt (energyInt J A (Metric.closedBall 0 R) (χ k)))) atTop (𝓝 0) := by
    simpa using ((hχM R φ hφ).add (hχE R).sqrt).const_mul C
  refine h1.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
  rw [Real.dist_eq, abs_sub_comm]
  exact hRC (χ k) (hχs k)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeIntegralMass.of_slices (hCP : ConeToProjective.Statement)
    (hS : SliceSectionMass.Statement) (hA : SectionHyperplaneAvoid.Statement)
    (hD : SectionDegreeSum.Statement) (hP : PointSliceMass.Statement) :
    ConeIntegralMass.Statement := by
  intro n e
  induction e with
  | zero =>
    intro δ h W f hW hf hδ
    obtain ⟨j, hj⟩ := hW.isRelevant
    have hℓ : linForm (Pi.single j (1 : ℂ)) ∉ W := by rwa [linForm_single]
    rw [hCP n 0 h W f (Pi.single j 1) (fun _ => 1) hW hf hℓ (fun _ _ _ => rfl) continuousOn_const]
    exact hP n δ h W f _ hW hf hδ hℓ
  | succ e ih =>
    intro δ h J f hJ hf hδ
    obtain ⟨j, hj⟩ := hJ.isRelevant
    have hu : linForm (Pi.single j (1 : ℂ)) ∉ J := by rwa [linForm_single]
    obtain ⟨ℓ, hℓ, hℓW⟩ := hA n J (Pi.single j 1) hJ
    obtain ⟨g, δW, hW, hsum⟩ := hD ℂ n e δ J f (Pi.single j 1) hJ hf hδ hu
    rw [hCP n (e + 1) h J f ℓ (fun _ => 1) hJ hf hℓ (fun _ _ _ => rfl) continuousOn_const,
      hS n e h J f (Pi.single j 1) ℓ hJ hf hu hℓ hℓW, hsum]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWc, hWδ⟩ := hW W hWm
    rw [← hCP n e h W (g W) ℓ (fun _ => 1) hWp hWc (hℓW W hWm) (fun _ _ _ => rfl)
      continuousOn_const, ih (δW W) h W (g W) hWp hWc hWδ]

theorem MassFromLelong.proof (hS : SliceSectionMass.Statement)
    (hA : SectionHyperplaneAvoid.Statement) (hD : SectionDegreeSum.Statement)
    (hP : PointSliceMass.Statement) : MassFromLelong.Statement :=
  fun _ _ _ _ _ hCP _ => ConeIntegralMass.of_slices hCP hS hA hD hP

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem PoincareLelong.proof (hStokes : StokesOnVariety.Statement)
    (hReg : LelongRegularise.Statement) (hLim : LelongLimit.Statement) :
    PoincareLelong.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ), varInt J (d + 1) f (vecCons (logReg u ε) φ) =
      varInt J (d + 1) (logReg u ε) (vecCons f φ) := fun ε hε =>
    hStokes n d J f (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hf)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hfc)
  exact tendsto_nhds_unique (hReg n d J u f φ hJ hdim hu hf hfc hφ)
    ((hLim n d J u f φ hJ hdim hu hf hfc hφ).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SectionDegreeSum.proof (h : ChowFormSection.Statement) : SectionDegreeSum.Statement := by
  intro F _ _ n e δ I f u hI hf hδ hu
  obtain ⟨c, hc, g, hg, heq⟩ := h F n (e + 1) I f u hI hf hu
  have hδs : IsMultiHomog δ (specFirst f u) := hδ.specFirst u
  rw [heq] at hδs
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hδs hne
  exact ⟨g, δW, fun W hW => ⟨isProjPrime_of_mem_support_divCycle hI u hW, hg W hW, hδW W hW⟩,
    hsum.symm⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SlabBound.proof : SlabBound.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceCutBoundary.proof (hB : SliceBoundaryBound.Statement) (hD : SliceCutDecay.Statement) :
    SliceCutBoundary.Statement := by
  intro n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨C, hC0, hC⟩ := hB n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨D, hDk⟩ := hD n e h W g ℓ A hW hg hℓ hA
  have h1 : Tendsto (fun k : ℕ => D / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun k : ℕ => C * (D / ((k : ℝ) + 1) + Real.sqrt (D / ((k : ℝ) + 1)))) atTop
      (𝓝 0) := by
    simpa using (h1.add h1.sqrt).const_mul C
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (hC _ (SliceCut.contDiff h k) (SliceCut.hasCompactSupport h k)).trans ?_
  obtain ⟨hm, he⟩ := hDk k
  gcongr

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceExhaustion.varInt_tendsto_sliceCut {n d : ℕ} (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ) (hM : SliceMassFinite.Statement)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d)
    (hsm : SmoothNear (zeroSet I) fun x => Real.log (h.dualNorm x)) :
    Tendsto (fun k => varInt I d (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) atTop
      (𝓝 (varInt I d (fun _ => 1) fun _ x => Real.log (h.dualNorm x))) := by
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection I A
  · simp only [varInt, dif_pos hA]
    have := CutOffDominated.proof n d I hA.choose 1 (sliceCut h) (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) hI hdim hA.choose_spec one_ne_zero (SliceCut.measurable h)
      (SliceCut.mem_Icc h) (fun x _ _ => SliceCut.tendsto_one h x) continuousOn_const (fun _ => hsm)
      (hM n d h I ℓ hA.choose hI hℓ hdim hA.choose_spec)
    simpa only [mul_one] using this
  · simp only [varInt, dif_neg hA]
    exact tendsto_const_nhds

theorem SliceExhaustion.proof (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement)
    (hM : SliceMassFinite.Statement) (hE : SliceLelongError.Statement) : SliceExhaustion.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨-, himg, -⟩ := hC n J u ℓ hJ hℓW
  have hmem1 : ∀ K : Ideal (MvPolynomial (Fin n) ℂ), linForm ℓ - 1 ∈ K ⊔ Ideal.span {linForm ℓ - 1} :=
    fun _ => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨sliceCut h, SliceCut.contDiff h, SliceCut.hasCompactSupport h, SliceCut.mem_Icc h,
    SliceCut.tendsto_one h,
    SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hprime (hmem1 J) hdim
      (smoothNear_log_dualNorm_slice h J ℓ), fun W hW => ?_, hE n e h J F u ℓ hJ hF hu hℓ hℓW⟩
  have hmin : W ⊔ Ideal.span {linForm ℓ - 1} ∈
      (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes := by
    rw [← himg]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hW)
  exact SliceExhaustion.varInt_tendsto_sliceCut h _ ℓ hM hmin.1.1 (hmem1 W)
    (IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hprime hdim (huJ u hu) hmin)
    (smoothNear_log_dualNorm_slice h W ℓ)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem VarSlabMeasure.proof (hV : VarietySlabMeasure.Statement) : VarSlabMeasure.Statement := by
  intro n d J u R hJ hd hu
  obtain ⟨C, α, -, hα, hb⟩ := hV n d J u hJ hd.le hu R
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  have hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} =
      {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact hb ε hε hε1

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem AffineChartTrdeg.full : GroundTheory.Heights₂.Heights.AffineChartTrdeg.Statement :=
  GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof

theorem AreaGraphPiece.full : GroundTheory.Heights₂.Heights.AreaGraphPiece.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphPiece.proof

theorem AreaGraphPartition.full : GroundTheory.Heights₂.Heights.AreaGraphPartition.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphPartition.proof

theorem GraphJacContinuous.full : GroundTheory.Heights₂.Heights.GraphJacContinuous.Statement :=
  GroundTheory.Heights₂.Heights.GraphJacContinuous.proof

theorem AreaGraphBound.full : GroundTheory.Heights₂.Heights.AreaGraphBound.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraphBound.proof GroundTheory.Heights₂.Heights.AreaGraphPiece.full GroundTheory.Heights₂.Heights.AreaGraphPartition.full GroundTheory.Heights₂.Heights.GraphJacContinuous.full

theorem AreaGraph.full : GroundTheory.Heights₂.Heights.AreaGraph.Statement :=
  GroundTheory.Heights₂.Heights.AreaGraph.proof GroundTheory.Heights₂.Heights.AreaGraphBound.full

theorem AreaLinear.full : GroundTheory.Heights₂.Heights.AreaLinear.Statement :=
  GroundTheory.Heights₂.Heights.AreaLinear.proof

theorem AreaMultiplicity.full : GroundTheory.Heights₂.Heights.AreaMultiplicity.Statement :=
  GroundTheory.Heights₂.Heights.AreaMultiplicity.proof

theorem CauchyBinetMinors.full : GroundTheory.Heights₂.Heights.CauchyBinetMinors.Statement :=
  GroundTheory.Heights₂.Heights.CauchyBinetMinors.proof

theorem ChartChoice.full : GroundTheory.Heights₂.Heights.ChartChoice.Statement :=
  GroundTheory.Heights₂.Heights.ChartChoice.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem ChartDehomog.full : GroundTheory.Heights₂.Heights.ChartDehomog.Statement :=
  GroundTheory.Heights₂.Heights.ChartDehomog.proof

theorem ChartFinite.full : GroundTheory.Heights₂.Heights.ChartFinite.Statement :=
  GroundTheory.Heights₂.Heights.ChartFinite.proof

theorem ChartFirstGroupDvd.full : GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.Statement :=
  GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full

theorem IncIdealBelow.full : GroundTheory.Heights₂.Heights.IncIdealBelow.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealBelow.proof GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem ChartFirstGroupPrime.full : GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.Statement :=
  GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.IncIdealBelow.full

theorem ChartHomogenise.full : GroundTheory.Heights₂.Heights.ChartHomogenise.Statement :=
  GroundTheory.Heights₂.Heights.ChartHomogenise.proof

theorem ChartIncDomain.full : GroundTheory.Heights₂.Heights.ChartIncDomain.Statement :=
  GroundTheory.Heights₂.Heights.ChartIncDomain.proof

theorem ChartIncOrd.full : GroundTheory.Heights₂.Heights.ChartIncOrd.Statement :=
  GroundTheory.Heights₂.Heights.ChartIncOrd.proof GroundTheory.Heights₂.Heights.OrdPolynomialLocalization.full

theorem ChartKernel.full : GroundTheory.Heights₂.Heights.ChartKernel.Statement :=
  GroundTheory.Heights₂.Heights.ChartKernel.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.ChartIncDomain.full

theorem SpecFirstMemIncIdeal.full : GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.Statement :=
  GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.proof

theorem LengthFiniteAlgebra.full : GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.Statement :=
  GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.proof

theorem IncIdealDim.full : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.full

theorem ConeDimOfChowForm.full : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem ComponentOfIncIdeal.full : GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.Statement :=
  GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ConeDimComponent.full

theorem ChartMaxIdeals.full : GroundTheory.Heights₂.Heights.ChartMaxIdeals.Statement :=
  GroundTheory.Heights₂.Heights.ChartMaxIdeals.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ChartHomogenise.full GroundTheory.Heights₂.Heights.ChartDehomog.full GroundTheory.Heights₂.Heights.ComponentOfIncIdeal.full

theorem ChowFormExists.full : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormExists.proof GroundTheory.Heights₂.Heights.IncIdealDim.full GroundTheory.Heights₂.Heights.IncIdealPrime.full

theorem DehomogOrd.full : GroundTheory.Heights₂.Heights.DehomogOrd.Statement :=
  GroundTheory.Heights₂.Heights.DehomogOrd.proof GroundTheory.Heights₂.Heights.OrdPolynomialLocalization.full

theorem LocalMultOrd.full : GroundTheory.Heights₂.Heights.LocalMultOrd.Statement :=
  GroundTheory.Heights₂.Heights.LocalMultOrd.proof

theorem ChartLocalOrder.full : GroundTheory.Heights₂.Heights.ChartLocalOrder.Statement :=
  GroundTheory.Heights₂.Heights.ChartLocalOrder.proof GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.ChartIncOrd.full GroundTheory.Heights₂.Heights.DehomogOrd.full GroundTheory.Heights₂.Heights.LocalMultOrd.full

theorem ChartResidueDegree.full : GroundTheory.Heights₂.Heights.ChartResidueDegree.Statement :=
  GroundTheory.Heights₂.Heights.ChartResidueDegree.proof GroundTheory.Heights₂.Heights.ChowFormBirational.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartKernel.full GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.ChartLocalOrder.full

theorem ChartLength.full : GroundTheory.Heights₂.Heights.ChartLength.Statement :=
  GroundTheory.Heights₂.Heights.ChartLength.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.LengthFiniteAlgebra.full GroundTheory.Heights₂.Heights.ChartMaxIdeals.full GroundTheory.Heights₂.Heights.ChartLocalOrder.full GroundTheory.Heights₂.Heights.ChartResidueDegree.full

theorem ChartLocDomain.full : GroundTheory.Heights₂.Heights.ChartLocDomain.Statement :=
  GroundTheory.Heights₂.Heights.ChartLocDomain.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.ChartIncDomain.full GroundTheory.Heights₂.Heights.ChartKernel.full

theorem SheetComass.full : GroundTheory.Heights₂.Heights.SheetComass.Statement :=
  GroundTheory.Heights₂.Heights.SheetComass.proof

theorem SheetImageArea.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.SheetImageArea.Statement :=
  GroundTheory.Heights₂.Heights.SheetImageArea.proof hSheetImageAreaSet

theorem SheetAreaCompare.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.SheetAreaCompare.Statement :=
  GroundTheory.Heights₂.Heights.SheetAreaCompare.proof (GroundTheory.Heights₂.Heights.SheetImageArea.of_open hSheetImageAreaSet)

theorem ChartMassCompare.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.ChartMassCompare.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompare.proof GroundTheory.Heights₂.Heights.SheetComass.full (GroundTheory.Heights₂.Heights.SheetAreaCompare.of_open hSheetImageAreaSet)

theorem ComplexSets.ConeAvoidsFinite.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof

theorem ComplexSets.FiniteProjHomInjective.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof

theorem ComplexSets.ConeAvoidsOpen.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof

theorem ComplexSets.LeadIdealDim.full : GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof

theorem ComplexSets.LinearFormCut.full : GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof

theorem ComplexSets.HomogDimZeroPow.full : GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof

theorem ComplexSets.ConeAvoidsExists.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.full GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.full GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.full

theorem ComplexSets.FiniteProjectionsContainOpen.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.full GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.full GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.full GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.full

theorem ComplexSets.UnitaryZariskiDense.full : GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof

theorem ComplexSets.GenericProjectionFinite.full : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.full GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.full

theorem ComplexSets.FibreBound.full : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

theorem ComplexSets.PrimitiveElementFibres.full : GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof

theorem ComplexSets.DiscriminantCover.full : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.full

theorem NullSmaller.full : GroundTheory.Heights₂.Heights.NullSmaller.Statement :=
  GroundTheory.Heights₂.Heights.NullSmaller.proof

theorem FrameJacobianSum.full : GroundTheory.Heights₂.Heights.FrameJacobianSum.Statement :=
  GroundTheory.Heights₂.Heights.FrameJacobianSum.proof

theorem GraphAreaHolomorphic.full : GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.Statement :=
  GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.proof GroundTheory.Heights₂.Heights.AreaGraph.full

theorem ProjectionFormula.full : GroundTheory.Heights₂.Heights.ProjectionFormula.Statement :=
  GroundTheory.Heights₂.Heights.ProjectionFormula.proof GroundTheory.Heights₂.Heights.AreaMultiplicity.full GroundTheory.Heights₂.Heights.FrameJacobianSum.full GroundTheory.Heights₂.Heights.GraphAreaHolomorphic.full

theorem LocalGraphMass.full : GroundTheory.Heights₂.Heights.LocalGraphMass.Statement :=
  GroundTheory.Heights₂.Heights.LocalGraphMass.proof GroundTheory.Heights₂.Heights.ProjectionFormula.full

theorem MassFinite.full : GroundTheory.Heights₂.Heights.MassFinite.Statement :=
  GroundTheory.Heights₂.Heights.MassFinite.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.NullSmaller.full GroundTheory.Heights₂.Heights.LocalGraphMass.full

theorem ChartMassCompact.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.ChartMassCompact.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompact.proof (GroundTheory.Heights₂.Heights.ChartMassCompare.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.MassFinite.full

theorem LocalizationPrimeDVR.full : GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.Statement :=
  GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.proof

theorem NormFormEval.full : GroundTheory.Heights₂.Heights.NormFormEval.Statement :=
  GroundTheory.Heights₂.Heights.NormFormEval.proof

theorem NormFormEmbeddings.full : GroundTheory.Heights₂.Heights.NormFormEmbeddings.Statement :=
  GroundTheory.Heights₂.Heights.NormFormEmbeddings.proof GroundTheory.Heights₂.Heights.NormFormEval.full

theorem LinearFormPrime.full : GroundTheory.Heights₂.Heights.LinearFormPrime.Statement :=
  GroundTheory.Heights₂.Heights.LinearFormPrime.proof

theorem MapDvdDescent.full : GroundTheory.Heights₂.Heights.MapDvdDescent.Statement :=
  GroundTheory.Heights₂.Heights.MapDvdDescent.proof

theorem NormFormDvd.full : GroundTheory.Heights₂.Heights.NormFormDvd.Statement :=
  GroundTheory.Heights₂.Heights.NormFormDvd.proof GroundTheory.Heights₂.Heights.NormFormEmbeddings.full GroundTheory.Heights₂.Heights.LinearFormPrime.full GroundTheory.Heights₂.Heights.MapDvdDescent.full

theorem PrimeMapFractionRing.full : GroundTheory.Heights₂.Heights.PrimeMapFractionRing.Statement :=
  GroundTheory.Heights₂.Heights.PrimeMapFractionRing.proof

theorem NormOfDividedForm.full : GroundTheory.Heights₂.Heights.NormOfDividedForm.Statement :=
  GroundTheory.Heights₂.Heights.NormOfDividedForm.proof GroundTheory.Heights₂.Heights.NormFormEval.full GroundTheory.Heights₂.Heights.NormFormDvd.full GroundTheory.Heights₂.Heights.PrimeMapFractionRing.full

theorem ChartNorm.full : GroundTheory.Heights₂.Heights.ChartNorm.Statement :=
  GroundTheory.Heights₂.Heights.ChartNorm.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartFirstGroupPrime.full GroundTheory.Heights₂.Heights.ChartFirstGroupDvd.full GroundTheory.Heights₂.Heights.NormOfDividedForm.full

theorem ChowFormDimLe.full : GroundTheory.Heights₂.Heights.ChowFormDimLe.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormDimLe.proof

theorem SpecFirstNe.full : GroundTheory.Heights₂.Heights.SpecFirstNe.Statement :=
  GroundTheory.Heights₂.Heights.SpecFirstNe.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartNorm.full

theorem EmultiplicityOrd.full : GroundTheory.Heights₂.Heights.EmultiplicityOrd.Statement :=
  GroundTheory.Heights₂.Heights.EmultiplicityOrd.proof GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full

theorem SectionOrder.full : GroundTheory.Heights₂.Heights.SectionOrder.Statement :=
  GroundTheory.Heights₂.Heights.SectionOrder.proof GroundTheory.Heights₂.Heights.IncIdealBelow.full GroundTheory.Heights₂.Heights.SpecFirstMemIncIdeal.full GroundTheory.Heights₂.Heights.ChartChoice.full GroundTheory.Heights₂.Heights.SpecFirstNe.full GroundTheory.Heights₂.Heights.LocalizationPrimeDVR.full GroundTheory.Heights₂.Heights.EmultiplicityOrd.full GroundTheory.Heights₂.Heights.ChartFinite.full GroundTheory.Heights₂.Heights.ChartLocDomain.full GroundTheory.Heights₂.Heights.ChartNorm.full GroundTheory.Heights₂.Heights.ChartLength.full GroundTheory.Heights₂.Heights.LengthQuotientDet.full

theorem ChowFormSection.full : GroundTheory.Heights₂.Heights.ChowFormSection.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormSection.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ConeDimComponent.full GroundTheory.Heights₂.Heights.ChowFormExists.full GroundTheory.Heights₂.Heights.IncIdealPrime.full GroundTheory.Heights₂.Heights.SectionOrder.full

theorem ComplexJacobian.full : GroundTheory.Heights₂.Heights.ComplexJacobian.Statement :=
  GroundTheory.Heights₂.Heights.ComplexJacobian.proof

theorem ComplexSets.BadSetSmaller.full : GroundTheory.Heights₂.Heights.ComplexSets.BadSetSmaller.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.BadSetSmaller.proof

theorem ComplexSets.ConeScaling.full : GroundTheory.Heights₂.Heights.ComplexSets.ConeScaling.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.ConeScaling.proof

theorem ComplexSets.FiniteProjectionsGeneric.full : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.full GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.full

theorem ComplexSets.FunctionFieldDegree.full : GroundTheory.Heights₂.Heights.ComplexSets.FunctionFieldDegree.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.FunctionFieldDegree.proof

theorem ComplexSets.GenericPrimitive.full : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.proof

theorem ComplexSets.SimpleRootBranch.full : GroundTheory.Heights₂.Heights.ComplexSets.SimpleRootBranch.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.SimpleRootBranch.proof

theorem SliceDim.full : GroundTheory.Heights₂.Heights.SliceDim.Statement :=
  GroundTheory.Heights₂.Heights.SliceDim.proof

theorem ConeSheetGram.of_open (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) :
    GroundTheory.Heights₂.Heights.ConeSheetGram.Statement :=
  GroundTheory.Heights₂.Heights.ConeSheetGram.proof hConeSheetGramLintegral

theorem ConeChartGram.of_open (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) :
    GroundTheory.Heights₂.Heights.ConeChartGram.Statement :=
  GroundTheory.Heights₂.Heights.ConeChartGram.proof (GroundTheory.Heights₂.Heights.ConeSheetGram.of_open hConeSheetGramLintegral) GroundTheory.Heights₂.Heights.MassFinite.full

theorem ConePolar.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) :
    GroundTheory.Heights₂.Heights.ConePolar.Statement :=
  GroundTheory.Heights₂.Heights.ConePolar.proof GroundTheory.Heights₂.Heights.SliceDim.full hLinearNoetherNormalization (GroundTheory.Heights₂.Heights.ConeChartGram.of_open hConeSheetGramLintegral)

theorem IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof

theorem SheetOnlyNull.full : GroundTheory.Heights₂.Heights.SheetOnlyNull.Statement :=
  GroundTheory.Heights₂.Heights.SheetOnlyNull.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full

theorem PosPartLocal.full : GroundTheory.Heights₂.Heights.PosPartLocal.Statement :=
  GroundTheory.Heights₂.Heights.PosPartLocal.proof

theorem PosPartSplit.full : GroundTheory.Heights₂.Heights.PosPartSplit.Statement :=
  GroundTheory.Heights₂.Heights.PosPartSplit.proof

theorem PosPartIndep.full : GroundTheory.Heights₂.Heights.PosPartIndep.Statement :=
  GroundTheory.Heights₂.Heights.PosPartIndep.proof GroundTheory.Heights₂.Heights.SheetOnlyNull.full GroundTheory.Heights₂.Heights.PosPartLocal.full GroundTheory.Heights₂.Heights.PosPartSplit.full

theorem IntegralIndep.full : GroundTheory.Heights₂.Heights.IntegralIndep.Statement :=
  GroundTheory.Heights₂.Heights.IntegralIndep.proof GroundTheory.Heights₂.Heights.PosPartIndep.full

theorem PlaneSliceMass.full : GroundTheory.Heights₂.Heights.PlaneSliceMass.Statement :=
  GroundTheory.Heights₂.Heights.PlaneSliceMass.proof GroundTheory.Heights₂.Heights.IntegralIndep.full

theorem ConeToProjective.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) :
    GroundTheory.Heights₂.Heights.ConeToProjective.Statement :=
  GroundTheory.Heights₂.Heights.ConeToProjective.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full (GroundTheory.Heights₂.Heights.ConePolar.of_open hLinearNoetherNormalization hConeSheetGramLintegral) GroundTheory.Heights₂.Heights.PlaneSliceMass.full

theorem StokesOffDiscriminant.full : GroundTheory.Heights₂.Heights.StokesOffDiscriminant.Statement :=
  GroundTheory.Heights₂.Heights.StokesOffDiscriminant.proof

theorem CutOffShape.full : GroundTheory.Heights₂.Heights.CutOffShape.Statement :=
  GroundTheory.Heights₂.Heights.CutOffShape.proof

theorem TubeFormCompare.full : GroundTheory.Heights₂.Heights.TubeFormCompare.Statement :=
  GroundTheory.Heights₂.Heights.TubeFormCompare.proof

theorem CutOffTube.of_open (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOffTube.Statement :=
  GroundTheory.Heights₂.Heights.CutOffTube.proof GroundTheory.Heights₂.Heights.TubeFormCompare.full hTubeEuclMass

theorem HessCCompPluri.full : GroundTheory.Heights₂.Heights.HessCCompPluri.Statement :=
  GroundTheory.Heights₂.Heights.HessCCompPluri.proof

theorem LogLogCutHess.full : GroundTheory.Heights₂.Heights.LogLogCutHess.Statement :=
  GroundTheory.Heights₂.Heights.LogLogCutHess.proof GroundTheory.Heights₂.Heights.HessCCompPluri.full

theorem CutOffGradient.full : GroundTheory.Heights₂.Heights.CutOffGradient.Statement :=
  GroundTheory.Heights₂.Heights.CutOffGradient.proof GroundTheory.Heights₂.Heights.LogLogCutHess.full

theorem CutOff.of_open (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOff.Statement :=
  GroundTheory.Heights₂.Heights.CutOff.proof GroundTheory.Heights₂.Heights.CutOffShape.full (GroundTheory.Heights₂.Heights.CutOffTube.of_open hTubeEuclMass) GroundTheory.Heights₂.Heights.CutOffGradient.full

theorem CutOffDominated.full : GroundTheory.Heights₂.Heights.CutOffDominated.Statement :=
  GroundTheory.Heights₂.Heights.CutOffDominated.proof

theorem MaDensLeibniz.full : GroundTheory.Heights₂.Heights.MaDensLeibniz.Statement :=
  GroundTheory.Heights₂.Heights.MaDensLeibniz.proof

theorem EnergyDensNonneg.full : GroundTheory.Heights₂.Heights.EnergyDensNonneg.Statement :=
  GroundTheory.Heights₂.Heights.EnergyDensNonneg.proof

theorem GradDensSheetBound.full : GroundTheory.Heights₂.Heights.GradDensSheetBound.Statement :=
  GroundTheory.Heights₂.Heights.GradDensSheetBound.proof

theorem CutOffBoundaryBound.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.CutOffBoundaryBound.Statement :=
  GroundTheory.Heights₂.Heights.CutOffBoundaryBound.proof (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.MaDensLeibniz.full GroundTheory.Heights₂.Heights.EnergyDensNonneg.full GroundTheory.Heights₂.Heights.GradDensSheetBound.full

theorem CutOffLimit.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.CutOffLimit.Statement :=
  GroundTheory.Heights₂.Heights.CutOffLimit.proof (GroundTheory.Heights₂.Heights.CutOff.of_open hTubeEuclMass) (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.CutOffDominated.full (GroundTheory.Heights₂.Heights.CutOffBoundaryBound.of_open hSheetImageAreaSet)

theorem StokesOnVariety.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.StokesOnVariety.Statement :=
  GroundTheory.Heights₂.Heights.StokesOnVariety.proof GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.StokesOffDiscriminant.full (GroundTheory.Heights₂.Heights.CutOffLimit.of_open hSheetImageAreaSet hTubeEuclMass)

theorem SheetSumMeasurable.full : GroundTheory.Heights₂.Heights.SheetSumMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof

theorem LocalGraphProjectionMass.full : GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.Statement :=
  GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.proof GroundTheory.Heights₂.Heights.ProjectionFormula.full

theorem VarietyProjectionMass.full : GroundTheory.Heights₂.Heights.VarietyProjectionMass.Statement :=
  GroundTheory.Heights₂.Heights.VarietyProjectionMass.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.LocalGraphProjectionMass.full

theorem IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.proof

theorem VarietySlabMeasure.full : GroundTheory.Heights₂.Heights.VarietySlabMeasure.Statement :=
  GroundTheory.Heights₂.Heights.VarietySlabMeasure.proof GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric.full GroundTheory.Heights₂.Heights.VarietyProjectionMass.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.full

theorem VarSlabMeasure.full : GroundTheory.Heights₂.Heights.VarSlabMeasure.Statement :=
  GroundTheory.Heights₂.Heights.VarSlabMeasure.proof GroundTheory.Heights₂.Heights.VarietySlabMeasure.full

theorem LogIntegrable.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.full (GroundTheory.Heights₂.Heights.ChartMassCompare.of_open hSheetImageAreaSet) GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.MassFinite.full

theorem LelongRegularise.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.LelongRegularise.Statement :=
  GroundTheory.Heights₂.Heights.LelongRegularise.proof (GroundTheory.Heights₂.Heights.LogIntegrable.of_open hSheetImageAreaSet)

theorem LelongLimitOffZero.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet)

theorem VarIntAdd.of_open (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  GroundTheory.Heights₂.Heights.VarIntAdd.proof (GroundTheory.Heights₂.Heights.ChartMassCompact.of_open hSheetImageAreaSet)

theorem LelongLimit.of_open (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) :
    GroundTheory.Heights₂.Heights.LelongLimit.Statement :=
  GroundTheory.Heights₂.Heights.LelongLimit.proof (GroundTheory.Heights₂.Heights.LelongLimitOffZero.of_open hSheetImageAreaSet) hLelongLimitOnZero (GroundTheory.Heights₂.Heights.VarIntAdd.of_open hSheetImageAreaSet)

theorem PoincareLelong.of_open (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.PoincareLelong.Statement :=
  GroundTheory.Heights₂.Heights.PoincareLelong.proof (GroundTheory.Heights₂.Heights.StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass) (GroundTheory.Heights₂.Heights.LelongRegularise.of_open hSheetImageAreaSet) (GroundTheory.Heights₂.Heights.LelongLimit.of_open hLelongLimitOnZero hSheetImageAreaSet)

theorem SliceIdeal.full : GroundTheory.Heights₂.Heights.SliceIdeal.Statement :=
  GroundTheory.Heights₂.Heights.SliceIdeal.proof

theorem SliceComponents.full : GroundTheory.Heights₂.Heights.SliceComponents.Statement :=
  GroundTheory.Heights₂.Heights.SliceComponents.proof

theorem SliceExhaustion.of_open (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) :
    GroundTheory.Heights₂.Heights.SliceExhaustion.Statement :=
  GroundTheory.Heights₂.Heights.SliceExhaustion.proof GroundTheory.Heights₂.Heights.SliceIdeal.full GroundTheory.Heights₂.Heights.SliceComponents.full hSliceMassFinite hSliceLelongError

theorem SliceSectionMass.of_open (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.SliceSectionMass.Statement :=
  GroundTheory.Heights₂.Heights.SliceSectionMass.proof (GroundTheory.Heights₂.Heights.StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass) (GroundTheory.Heights₂.Heights.PoincareLelong.of_open hLelongLimitOnZero hSheetImageAreaSet hTubeEuclMass) GroundTheory.Heights₂.Heights.SliceIdeal.full GroundTheory.Heights₂.Heights.SliceComponents.full (GroundTheory.Heights₂.Heights.SliceExhaustion.of_open hSliceLelongError hSliceMassFinite)

theorem SectionHyperplaneAvoid.full : GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid.Statement :=
  GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid.proof

theorem SectionDegreeSum.full : GroundTheory.Heights₂.Heights.SectionDegreeSum.Statement :=
  GroundTheory.Heights₂.Heights.SectionDegreeSum.proof GroundTheory.Heights₂.Heights.ChowFormSection.full

theorem PointSliceMass.full : GroundTheory.Heights₂.Heights.PointSliceMass.Statement :=
  GroundTheory.Heights₂.Heights.PointSliceMass.proof

theorem ConeIntegralMass.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.ConeIntegralMass.Statement :=
  GroundTheory.Heights₂.Heights.ConeIntegralMass.of_slices (GroundTheory.Heights₂.Heights.ConeToProjective.of_open hLinearNoetherNormalization hConeSheetGramLintegral) (GroundTheory.Heights₂.Heights.SliceSectionMass.of_open hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid.full GroundTheory.Heights₂.Heights.SectionDegreeSum.full GroundTheory.Heights₂.Heights.PointSliceMass.full

theorem ConeBallFinite.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.ConeBallFinite.Statement :=
  GroundTheory.Heights₂.Heights.ConeBallFinite.proof (GroundTheory.Heights₂.Heights.ConeIntegralMass.of_open hLinearNoetherNormalization hConeSheetGramLintegral hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass)

theorem ConeSlabBound.full : GroundTheory.Heights₂.Heights.ConeSlabBound.Statement :=
  GroundTheory.Heights₂.Heights.ConeSlabBound.proof GroundTheory.Heights₂.Heights.VarietySlabMeasure.full

theorem ConeFsLogIntegrable.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.ConeFsLogIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.ConeFsLogIntegrable.proof (GroundTheory.Heights₂.Heights.ConeBallFinite.of_open hLinearNoetherNormalization hConeSheetGramLintegral hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) GroundTheory.Heights₂.Heights.ConeSlabBound.full

theorem ZeroLocusDimH.full : GroundTheory.Heights₂.Heights.ZeroLocusDimH.Statement :=
  GroundTheory.Heights₂.Heights.ZeroLocusDimH.proof

theorem ConeHyperplaneNull.full : GroundTheory.Heights₂.Heights.ConeHyperplaneNull.Statement :=
  GroundTheory.Heights₂.Heights.ConeHyperplaneNull.proof GroundTheory.Heights₂.Heights.ZeroLocusDimH.full GroundTheory.Heights₂.Heights.ChowFormDimLe.full

theorem FormIntLelong.of_open (hChowFormSectionAlgClosed : GroundTheory.Heights₂.Heights.ChowFormSectionAlgClosed.Statement) (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hFormIntSlice : GroundTheory.Heights₂.Heights.FormIntSlice.Statement) (hSliceFormLelong : GroundTheory.Heights₂.Heights.SliceFormLelong.Statement) :
    GroundTheory.Heights₂.Heights.FormIntLelong.Statement :=
  GroundTheory.Heights₂.Heights.FormIntLelong.proof (GroundTheory.Heights₂.Heights.ConeToProjective.of_open hLinearNoetherNormalization hConeSheetGramLintegral) hChowFormSectionAlgClosed hFormIntSlice hSliceFormLelong

theorem SliceFormMass.of_open (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) :
    GroundTheory.Heights₂.Heights.SliceFormMass.Statement :=
  GroundTheory.Heights₂.Heights.SliceFormMass.proof GroundTheory.Heights₂.Heights.SliceIdeal.full hSliceMassFinite hSheetFormCompare

theorem SheetLogNormDens.full : GroundTheory.Heights₂.Heights.SheetLogNormDens.Statement :=
  GroundTheory.Heights₂.Heights.SheetLogNormDens.proof

theorem FormIntPos.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) :
    GroundTheory.Heights₂.Heights.FormIntPos.Statement :=
  GroundTheory.Heights₂.Heights.FormIntPos.proof (GroundTheory.Heights₂.Heights.ConeToProjective.of_open hLinearNoetherNormalization hConeSheetGramLintegral) (GroundTheory.Heights₂.Heights.SliceFormMass.of_open hSheetFormCompare hSliceMassFinite) GroundTheory.Heights₂.Heights.SheetLogNormDens.full

theorem SliceCutBoundary.of_open (hSliceBoundaryBound : GroundTheory.Heights₂.Heights.SliceBoundaryBound.Statement) (hSliceCutDecay : GroundTheory.Heights₂.Heights.SliceCutDecay.Statement) :
    GroundTheory.Heights₂.Heights.SliceCutBoundary.Statement :=
  GroundTheory.Heights₂.Heights.SliceCutBoundary.proof hSliceBoundaryBound hSliceCutDecay

theorem SliceCutOffLimit.of_open (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSliceBoundaryBound : GroundTheory.Heights₂.Heights.SliceBoundaryBound.Statement) (hSliceCutDecay : GroundTheory.Heights₂.Heights.SliceCutDecay.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) :
    GroundTheory.Heights₂.Heights.SliceCutOffLimit.Statement :=
  GroundTheory.Heights₂.Heights.SliceCutOffLimit.proof GroundTheory.Heights₂.Heights.SliceIdeal.full (GroundTheory.Heights₂.Heights.SliceFormMass.of_open hSheetFormCompare hSliceMassFinite) (GroundTheory.Heights₂.Heights.SliceCutBoundary.of_open hSliceBoundaryBound hSliceCutDecay)

theorem FormIntSymm.of_open (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceBoundaryBound : GroundTheory.Heights₂.Heights.SliceBoundaryBound.Statement) (hSliceCutDecay : GroundTheory.Heights₂.Heights.SliceCutDecay.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.FormIntSymm.Statement :=
  GroundTheory.Heights₂.Heights.FormIntSymm.proof GroundTheory.Heights₂.Heights.SliceIdeal.full (GroundTheory.Heights₂.Heights.StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass) (GroundTheory.Heights₂.Heights.SliceCutOffLimit.of_open hSheetFormCompare hSliceBoundaryBound hSliceCutDecay hSliceMassFinite)

theorem RegConeLimit.of_open (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.RegConeLimit.Statement :=
  GroundTheory.Heights₂.Heights.RegConeLimit.proof (GroundTheory.Heights₂.Heights.ConeBallFinite.of_open hLinearNoetherNormalization hConeSheetGramLintegral hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) (GroundTheory.Heights₂.Heights.ConeFsLogIntegrable.of_open hLinearNoetherNormalization hConeSheetGramLintegral hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) GroundTheory.Heights₂.Heights.ConeHyperplaneNull.full

theorem GreenFromLelong.of_open (hChowFormSectionAlgClosed : GroundTheory.Heights₂.Heights.ChowFormSectionAlgClosed.Statement) (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hFormIntSlice : GroundTheory.Heights₂.Heights.FormIntSlice.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceBoundaryBound : GroundTheory.Heights₂.Heights.SliceBoundaryBound.Statement) (hSliceCutDecay : GroundTheory.Heights₂.Heights.SliceCutDecay.Statement) (hSliceFormLelong : GroundTheory.Heights₂.Heights.SliceFormLelong.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.GreenFromLelong.Statement :=
  GroundTheory.Heights₂.Heights.GreenFromLelong.proof (GroundTheory.Heights₂.Heights.FormIntSymm.of_open hSheetFormCompare hSheetImageAreaSet hSliceBoundaryBound hSliceCutDecay hSliceMassFinite hTubeEuclMass) (GroundTheory.Heights₂.Heights.FormIntPos.of_open hLinearNoetherNormalization hConeSheetGramLintegral hSheetFormCompare hSliceMassFinite) (GroundTheory.Heights₂.Heights.FormIntLelong.of_open hChowFormSectionAlgClosed hLinearNoetherNormalization hConeSheetGramLintegral hFormIntSlice hSliceFormLelong) (GroundTheory.Heights₂.Heights.RegConeLimit.of_open hLinearNoetherNormalization hConeSheetGramLintegral hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) hChowFormSectionAlgClosed

theorem GreenSymmetry.of_open (hChowFormSectionAlgClosed : GroundTheory.Heights₂.Heights.ChowFormSectionAlgClosed.Statement) (hLinearNoetherNormalization : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement) (hConeSheetGramLintegral : GroundTheory.Heights₂.Heights.ConeSheetGramLintegral.Statement) (hFormIntSlice : GroundTheory.Heights₂.Heights.FormIntSlice.Statement) (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetFormCompare : GroundTheory.Heights₂.Heights.SheetFormCompare.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceBoundaryBound : GroundTheory.Heights₂.Heights.SliceBoundaryBound.Statement) (hSliceCutDecay : GroundTheory.Heights₂.Heights.SliceCutDecay.Statement) (hSliceFormLelong : GroundTheory.Heights₂.Heights.SliceFormLelong.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.GreenSymmetry.Statement :=
  (GroundTheory.Heights₂.Heights.GreenFromLelong.of_open hChowFormSectionAlgClosed hLinearNoetherNormalization hConeSheetGramLintegral hFormIntSlice hLelongLimitOnZero hSheetFormCompare hSheetImageAreaSet hSliceBoundaryBound hSliceCutDecay hSliceFormLelong hSliceLelongError hSliceMassFinite hTubeEuclMass) GroundTheory.Heights₂.Heights.IntegralIndep.full (GroundTheory.Heights₂.Heights.CutOff.of_open hTubeEuclMass) (GroundTheory.Heights₂.Heights.StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass) (GroundTheory.Heights₂.Heights.LogIntegrable.of_open hSheetImageAreaSet) (GroundTheory.Heights₂.Heights.PoincareLelong.of_open hLelongLimitOnZero hSheetImageAreaSet hTubeEuclMass) (GroundTheory.Heights₂.Heights.ConeToProjective.of_open hLinearNoetherNormalization hConeSheetGramLintegral)

theorem ImplicitCurve.full : GroundTheory.Heights₂.Heights.ImplicitCurve.Statement :=
  GroundTheory.Heights₂.Heights.ImplicitCurve.proof

theorem LineSliceMass.full : GroundTheory.Heights₂.Heights.LineSliceMass.Statement :=
  GroundTheory.Heights₂.Heights.PlaneSliceMass.line GroundTheory.Heights₂.Heights.PlaneSliceMass.full

theorem MassFromLelong.of_open (hLelongLimitOnZero : GroundTheory.Heights₂.Heights.LelongLimitOnZero.Statement) (hSheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement) (hSliceLelongError : GroundTheory.Heights₂.Heights.SliceLelongError.Statement) (hSliceMassFinite : GroundTheory.Heights₂.Heights.SliceMassFinite.Statement) (hTubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement) :
    GroundTheory.Heights₂.Heights.MassFromLelong.Statement :=
  GroundTheory.Heights₂.Heights.MassFromLelong.proof (GroundTheory.Heights₂.Heights.SliceSectionMass.of_open hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError hSliceMassFinite hTubeEuclMass) GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid.full GroundTheory.Heights₂.Heights.SectionDegreeSum.full GroundTheory.Heights₂.Heights.PointSliceMass.full

theorem PointIntegral.full : GroundTheory.Heights₂.Heights.PointIntegral.Statement :=
  GroundTheory.Heights₂.Heights.PointIntegral.proof

theorem PolySublevel.full : GroundTheory.Heights₂.Heights.PolySublevel.Statement :=
  GroundTheory.Heights₂.Heights.PolySublevel.proof

theorem SlabBound.full : GroundTheory.Heights₂.Heights.SlabBound.Statement :=
  GroundTheory.Heights₂.Heights.SlabBound.proof

theorem SliceMatricesOpen.full : GroundTheory.Heights₂.Heights.SliceMatricesOpen.Statement :=
  GroundTheory.Heights₂.Heights.SliceMatricesOpen.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.dividedDifference_real_holds

theorem IndefiniteRowSideFullHecke.ComplexSets.ContinuousRootHolomorphic.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ContinuousRootHolomorphic.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ContinuousRootHolomorphic.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.ProjectionCoordinateEquation.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjectionCoordinateEquation.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjectionCoordinateEquation.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionPolynomial.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionPolynomial.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.ContinuousSectionHolomorphic.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ContinuousSectionHolomorphic.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ContinuousSectionHolomorphic.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjectionCoordinateEquation.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ContinuousRootHolomorphic.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionPolynomial.full

theorem IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full

theorem IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full

theorem IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreSectionsCovering.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc.full

theorem IndefiniteRowSideFullHecke.ComplexSets.RemovableHyperplane.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RemovableHyperplane.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RemovableHyperplane.proof

theorem IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full

theorem IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem ConeAreaFormula.of_open (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) :
    GroundTheory.Heights₂.Heights.ConeAreaFormula.Statement :=
  GroundTheory.Heights₂.Heights.ConeAreaFormula.proof hConeGraphCover hGraphAreaFibre

theorem ConeLocalMass.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) :
    GroundTheory.Heights₂.Heights.ConeLocalMass.Statement :=
  GroundTheory.Heights₂.Heights.ConeLocalMass.proof hConeFiniteFibreDim GroundTheory.Heights₂.Heights.MassFinite.full GroundTheory.Heights₂.Heights.NullSmaller.full

theorem ConeTangentAverage.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeTangentAverage.Statement :=
  GroundTheory.Heights₂.Heights.ConeTangentAverage.proof (GroundTheory.Heights₂.Heights.ConeLocalMass.of_open hConeFiniteFibreDim) hConeJacMeasurable hConeTangentDim hTangentGaussInvariant

theorem ConeRadialIntegral.full : GroundTheory.Heights₂.Heights.ConeRadialIntegral.Statement :=
  GroundTheory.Heights₂.Heights.ConeRadialIntegral.proof

theorem LeadPlaneJac.full : GroundTheory.Heights₂.Heights.LeadPlaneJac.Statement :=
  GroundTheory.Heights₂.Heights.LeadPlaneJac.proof

theorem LeadBlockGaussTail.full : GroundTheory.Heights₂.Heights.LeadBlockGaussTail.Statement :=
  GroundTheory.Heights₂.Heights.LeadBlockGaussTail.proof

theorem TangentGaussMoment.full : GroundTheory.Heights₂.Heights.TangentGaussMoment.Statement :=
  GroundTheory.Heights₂.Heights.TangentGaussMoment.proof GroundTheory.Heights₂.Heights.LeadPlaneJac.full GroundTheory.Heights₂.Heights.LeadBlockGaussTail.full

theorem ConeFibreAverage.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeFibreAverage.Statement :=
  GroundTheory.Heights₂.Heights.ConeFibreAverage.proof (GroundTheory.Heights₂.Heights.ConeAreaFormula.of_open hConeGraphCover hGraphAreaFibre) (GroundTheory.Heights₂.Heights.ConeTangentAverage.of_open hConeFiniteFibreDim hConeJacMeasurable hConeTangentDim hTangentGaussInvariant) GroundTheory.Heights₂.Heights.ConeRadialIntegral.full GroundTheory.Heights₂.Heights.TangentGaussMoment.full

theorem ProjSecDegree.full : GroundTheory.Heights₂.Heights.ProjSecDegree.Statement :=
  GroundTheory.Heights₂.Heights.ProjSecDegree.proof

theorem ProjSecDomain.full : GroundTheory.Heights₂.Heights.ProjSecDomain.Statement :=
  GroundTheory.Heights₂.Heights.ProjSecDomain.proof

theorem ProjChowNonzero.full : GroundTheory.Heights₂.Heights.ProjChowNonzero.Statement :=
  GroundTheory.Heights₂.Heights.ProjChowNonzero.proof

theorem SecDegreeLe.full : GroundTheory.Heights₂.Heights.SecDegreeLe.Statement :=
  GroundTheory.Heights₂.Heights.SecDegreeLe.proof

theorem SecFiniteUnit.full : GroundTheory.Heights₂.Heights.SecFiniteUnit.Statement :=
  GroundTheory.Heights₂.Heights.SecFiniteUnit.proof

theorem SecRankSpecialize.full : GroundTheory.Heights₂.Heights.SecRankSpecialize.Statement :=
  GroundTheory.Heights₂.Heights.SecRankSpecialize.proof

theorem SecDegreeGe.full : GroundTheory.Heights₂.Heights.SecDegreeGe.Statement :=
  GroundTheory.Heights₂.Heights.SecDegreeGe.proof GroundTheory.Heights₂.Heights.SecFiniteUnit.full GroundTheory.Heights₂.Heights.SecRankSpecialize.full

theorem ProjDegreeChow.full : GroundTheory.Heights₂.Heights.ProjDegreeChow.Statement :=
  GroundTheory.Heights₂.Heights.ProjDegreeChow.proof GroundTheory.Heights₂.Heights.ProjSecDegree.full GroundTheory.Heights₂.Heights.ProjSecDomain.full GroundTheory.Heights₂.Heights.ProjChowNonzero.full GroundTheory.Heights₂.Heights.SecDegreeLe.full GroundTheory.Heights₂.Heights.SecDegreeGe.full

theorem ConeFibreDegree.full : GroundTheory.Heights₂.Heights.ConeFibreDegree.Statement :=
  GroundTheory.Heights₂.Heights.ConeFibreDegree.proof GroundTheory.Heights₂.Heights.ConeDimOfChowForm.full GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full GroundTheory.Heights₂.Heights.ProjDegreeChow.full

theorem ConeMassOfFibre.of_open (hConeFiniteFibreDim : GroundTheory.Heights₂.Heights.ConeFiniteFibreDim.Statement) (hConeGraphCover : GroundTheory.Heights₂.Heights.ConeGraphCover.Statement) (hConeJacMeasurable : GroundTheory.Heights₂.Heights.ConeJacMeasurable.Statement) (hConeTangentDim : GroundTheory.Heights₂.Heights.ConeTangentDim.Statement) (hGraphAreaFibre : GroundTheory.Heights₂.Heights.GraphAreaFibre.Statement) (hTangentGaussInvariant : GroundTheory.Heights₂.Heights.TangentGaussInvariant.Statement) :
    GroundTheory.Heights₂.Heights.ConeMassOfFibre.Statement :=
  GroundTheory.Heights₂.Heights.ConeMassOfFibre.proof (GroundTheory.Heights₂.Heights.ConeFibreAverage.of_open hConeFiniteFibreDim hConeGraphCover hConeJacMeasurable hConeTangentDim hGraphAreaFibre hTangentGaussInvariant)

end GroundTheory.Heights₂.Heights
end
