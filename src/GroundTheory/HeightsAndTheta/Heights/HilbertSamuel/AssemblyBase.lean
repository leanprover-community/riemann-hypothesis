import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepWeightMass
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResNullForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalCoordinates
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHeightsirationalHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockChiCovolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageMetrics
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConjIntNum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegMatAct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenFibreHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedMixedNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNonzeroSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedOne
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramChiDerivative
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometricForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SaturatedSaturation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneRegularSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntNumComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLatticeCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HasDerivAtDet
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedTopAlgebra
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonnegAtZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolySandwich
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameBasePtFree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtTransc
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatNoetherFrame
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatioFieldDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionComplex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionInterpIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecCochReduce
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionProduct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftIntersectionPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallBallVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTranscRatioDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCoeffCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockHorizDiv
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseResolution
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.Intersections.DetRestrictScalarsEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockGenFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreIsolFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.SpanSingletonEqRangeLsmul
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRegCurvBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntPoint
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.BergmanLerpSelf
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PProjDegGenDeg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegrePartition

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

theorem BetaSum.proof : BetaSum.Statement := by
  intro D i hi

  set I : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ (D - i) with hIdef
  have hB : Complex.betaIntegral ((i : ℂ) + 1) (((D - i : ℕ) : ℂ) + 1) = (I : ℂ) := by
    rw [Complex.betaIntegral, hIdef, ← intervalIntegral.integral_ofReal]
    congr 1
    ext x
    rw [add_sub_cancel_right, add_sub_cancel_right, Complex.cpow_natCast, Complex.cpow_natCast]
    push_cast
    ring
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (i : ℂ) + 1)
    (t := ((D - i : ℕ) : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have hst : (i : ℂ) + 1 + (((D - i : ℕ) : ℂ) + 1) = ((D + 1 : ℕ) : ℂ) + 1 := by
    push_cast [Nat.cast_sub hi]
    ring
  rw [hst, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, hB] at hG
  have hR : (i.factorial : ℝ) * (D - i).factorial = (D + 1).factorial * I := by
    exact_mod_cast hG

  have hc : (D.choose i : ℝ) * i.factorial * (D - i).factorial = D.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  have hpos : (0 : ℝ) < D.factorial := by positivity
  have hint : ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i)
      = (D.choose i : ℝ) * I := by
    rw [hIdef, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [hint, eq_div_iff (by positivity)]
  apply mul_right_cancel₀ hpos.ne'
  calc (D.choose i : ℝ) * I * ((D : ℝ) + 1) * D.factorial
      = (D.choose i : ℝ) * ((D + 1).factorial * I) := by rw [hf]; ring
    _ = (D.choose i : ℝ) * i.factorial * (D - i).factorial := by rw [← hR]; ring
    _ = 1 * D.factorial := by rw [hc, one_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SupBoundCount

noncomputable section

theorem BlockResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    BlockResolutionFormsIndependent.Statement := by
  intro D K _ _ ι _ Ω _ _ d n r b hb a ha
  choose f hf hbf using hb.1
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg

  set F : ((Σ k, ι k) → ℂ) → ℂ := fun z => ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) with hF
  have ha' : ∀ x : d.R.X, F (blockPt d x) = 0 := by
    intro x
    have := ha x
    simp only [hbf, eval_map_int_rat] at this
    exact this
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb.2.1
    simp only [hbf, aeval_map_int] at this
    exact this
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)

  have hev : ∀ (s : MRing ι) (e : K → ℕ), IsMultiHomog s e → ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
        (∏ k, c k ^ e k) * eval z (map (Int.castRingHom ℂ) s) := by
    intro s e hs c z
    rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : (∏ i : (Σ k, ι k), c i.1 ^ m i) = ∏ k, c k ^ e k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
    simp only [mul_pow, Finset.prod_mul_distrib, hc]
    ring

  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      F (fun p => c p.1 * z p) = (∏ k, c k ^ blockDeg d.k₀ n k) * F z := by
    intro c z
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev (f k) _ (hf k) c z]
    ring

  have hoff : ∀ z, z ∈ mcPts (mCoordIdeal d.y) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨x, c, hc, hxz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 := ha' x
    rw [show blockPt d x = d.R.lift x x from rfl, hxz, hsmul] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))

  have hpts : ∀ z ∈ mcPts (mCoordIdeal d.y), F z = 0 := by
    intro z hz
    have hcl := hND K ι (mCoordIdeal d.y) (D + 1) g d.arith hgP hz
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 (fun z' hz' => hoff z' hz'.1 hz'.2) hcl
  exact coeff_eq_zero hli (mcPts_nonempty d) hpts

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem DoubleComplexVanish.proof : DoubleComplexVanish.Statement := by
  intro C _ P δ κ R hδP hκP hδδ hδκ hκκ hsurj hex hzero hacyc

  have triv : ∀ p n, R ≤ p → ∀ x ∈ P p (n + 1), (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    rintro p n hp x - ⟨y, hy, rfl⟩
    rw [hzero (p + 1) (n + 1) (by omega) y hy, map_zero]
    exact ⟨0, zero_mem _, map_zero _, 0, zero_mem _, map_zero _⟩
  have claim : ∀ k p n, R ≤ p + k → ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 →
      (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    intro k
    induction k with
    | zero => exact fun p n hp x hx _ hy => triv p n (by omega) x hx hy
    | succ k ih =>
      intro p n hp x hx hdx hy0
      by_cases hRp : R ≤ p
      · exact triv p n hRp x hx hy0
      obtain ⟨y, hy, hyx⟩ := hy0
      have hdy : δ (p + 1) (n + 1) y ∈ P (p + 1) (n + 2) := hδP _ _ y hy
      have hk : κ p (n + 2) (δ (p + 1) (n + 1) y) = 0 := by
        rw [← hδκ p (n + 1) y hy, hyx, hdx]
      obtain ⟨w, hw, hwe, w', hw', hw'e⟩ :=
        ih (p + 1) (n + 1) (by omega) _ hdy (hδδ _ _ y hy) (hex p (n + 2) _ hdy hk)
      have hdyw : δ (p + 1) (n + 1) (y - w) = 0 := by rw [map_sub, hwe, sub_self]
      obtain ⟨v, hv, hve⟩ := hacyc (p + 1) (by omega) (by omega) n (y - w) (sub_mem hy hw) hdyw
      refine ⟨κ p n v, hκP _ _ v hv, ?_, v, hv, rfl⟩
      rw [hδκ p n v hv, hve, map_sub, hyx, ← hw'e, hκκ p (n + 1) w' hw', sub_zero]
  intro n x hx hdx
  obtain ⟨w, hw, hwe, -⟩ := claim R 0 n (by omega) x hx hdx (hsurj (n + 1) x hx)
  exact ⟨w, hw, hwe⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

theorem GeneratedMixedNonneg.proof (hGP : GeneratedProductNonneg.Statement) :
    GeneratedMixedNonneg.Statement := by
  intro F _ K _ _ ι _ _ V n bs hV hgen
  exact hGP F K ι (fun V _ L => NumbersDVR.intNum F V L) V n bs
    (NumbersDVR.IntNumIsFieldIntersection.full F K ι) hV hgen

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

theorem Halving.eventually_le (a : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |a n| ≤ C)
    (hh : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0))
    (hs : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)) (k : ℕ) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| ≤ C / 2 ^ k + ε := by
  induction k with
  | zero =>
    intro ε hε
    exact ⟨0, fun n _ ↦ by simpa using (hC n).trans (by linarith)⟩
  | succ k ih =>
    intro ε hε
    obtain ⟨N, hN⟩ := ih (ε / 4) (by positivity)
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hh (ε / 4) (by positivity)
    obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp hs (ε / 4) (by positivity)
    refine ⟨2 * (N + M₁ + M₂), fun m hm ↦ ?_⟩
    have hpow : C / 2 ^ (k + 1) = C / 2 ^ k / 2 := by rw [pow_succ, div_div]

    have even : ∀ n ≥ N + M₁ + M₂, |a (2 * n)| ≤ C / 2 ^ (k + 1) + ε / 2 := by
      intro n hn
      have h1 := hN n (by omega)
      have h2 := hM₁ n (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : |a (2 * n)| ≤ |a (2 * n) - a n / 2| + |a n| / 2 := by
        have := abs_add_le (a (2 * n) - a n / 2) (a n / 2)
        rw [sub_add_cancel, abs_div, abs_two] at this
        exact this
      rw [hpow]
      linarith
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · exact (even n (by omega)).trans (by linarith)
    · have he := even n (by omega)
      have h4 := hM₂ (2 * n) (by omega)
      rw [Real.dist_eq, sub_zero] at h4
      have h5 : |a (2 * n + 1)| ≤ |a (2 * n + 1) - a (2 * n)| + |a (2 * n)| := by
        have := abs_add_le (a (2 * n + 1) - a (2 * n)) (a (2 * n))
        rwa [sub_add_cancel] at this
      linarith

theorem Halving.proof : Halving.Statement := by
  intro a ⟨C, hC⟩ hh hs
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C / 2 ^ k < ε / 2 := by
    have ht : Tendsto (fun k : ℕ ↦ C / 2 ^ k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).const_mul C
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists
  obtain ⟨N, hN⟩ := Halving.eventually_le a C hC hh hs k (ε / 4) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  linarith [hN n hn]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

universe u v

theorem HilbertModule.proof (hMP : ModulesFromPrimes.Statement.{u, v})
    (hHP : HilbertPrime.Statement.{u}) : HilbertModule.Statement.{u, v} :=
  fun d => hMP d fun e _ => hHP e

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem LogDetDerivative.proof : LogDetDerivative.Statement :=
  LogDetDerivative.intersectionNumber_baseChange

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

theorem PolyNonnegAtZero.proof : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage

open ProjFrameImage in

theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 (fun z' hz' => hoff z' hz'.1 hz'.2) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SecCochReduce.map_map_int {K : Type} {ι : K → Type} (p : ℕ) (f : MRing ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.map (Int.castRingHom ℤ) f) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) f := by
  rw [MvPolynomial.map_map]
  congr 1

theorem SecCochReduce.proof : SecCochReduce.Statement := by
  intro K _ _ ι _ _ Ω _ y p a s hs
  funext J
  rw [FibreReduction.redCoch_apply]
  by_cases hz : ∃ k, y ⟨k, GenOnFibres.cellChart J k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    have := GenOnFibres.subsingleton_loc (S := ZMod p) (GenOnFibres.cellChart_mem J k) h0
    exact Subsingleton.elim _ _
  · push Not at hz
    obtain ⟨e, F, hF, _, heq⟩ := GenOnFibres.secCoch_spec (S := ℤ) hs J hz
    have hrep : GenOnFibres.IsRep y (ZMod p) (KH.cellMon (ZMod p) J.1)
        (FibreReduction.redLoc y p J.1 (GenOnFibres.secCoch y ℤ s a J)) (GenOnFibres.cellChart J) s a := by
      refine ⟨e, F, hF, GenOnFibres.cmon_mem (ZMod p) (GenOnFibres.cellChart_mem J) e, ?_⟩
      rw [heq, FibreReduction.redLoc_mk, FibreReduction.redRing_mk, SecCochReduce.map_map_int]
      congr 1
      exact Subtype.ext (SecCochReduce.map_map_int p _)
    exact hrep.unique (GenOnFibres.secCoch_spec hs J hz)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

theorem Weight.lerp_self_zero {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) : W.lerp W 0 = W := by
  cases W
  simp only [Weight.lerp, zero_mul, add_zero]

theorem SupNormAgainstL2.proof (h : UniformBergmanBound.Statement) : SupNormAgainstL2.Statement := by
  intro D X _ _ _ _ _ A L W dV hW
  obtain ⟨C, hC⟩ := h A L W W dV hW hW
  refine ⟨⟨Real.sqrt C, fun n hn s hs x => ?_⟩, fun n s hs M hM => ?_⟩
  · set V : Submodule ℂ (Fin A.n → X → ℂ) := ℂ ∙ s
    have hV : V ≤ L.sections n := (Submodule.span_singleton_le_iff_mem _ _).2 hs
    have hB := hC n hn 0 ⟨le_rfl, zero_le_one⟩ V hV x
    rw [Weight.lerp_self_zero] at hB
    set r := ptNormSq W n s x / sectionL2NormSq W dV n s
    have hr0 : 0 ≤ r := div_nonneg (ptNormSq_nonneg W n s x) (sectionL2NormSq_nonneg W dV n s)
    have hbdd : BddAbove (range fun v : V => ptNormSq W n (v : Fin A.n → X → ℂ) x /
        sectionL2NormSq W dV n v) := by
      refine ⟨r, ?_⟩
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp only [ptNormSq_smul, sectionL2NormSq_smul]
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hr0
      · rw [mul_div_mul_left _ _ (by positivity)]
    have hle : r ≤ bergman W dV V n x :=
      le_ciSup hbdd (⟨s, Submodule.mem_span_singleton_self s⟩ : V)
    have hrC : r ≤ C * (n : ℝ) ^ D := hle.trans hB
    rcases (sectionL2NormSq_nonneg W dV n s).eq_or_lt with h0 | hpos
    · rw [ptNormSq_eq_zero_of_l2NormSq_eq_zero W dV hs h0.symm x, Real.sqrt_zero]
      positivity
    · have hpt : ptNormSq W n s x ≤ C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s) := by
        rw [← mul_assoc, ← div_le_iff₀ hpos]; exact hrC
      calc Real.sqrt (ptNormSq W n s x)
          ≤ Real.sqrt (C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s)) := Real.sqrt_le_sqrt hpt
        _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s) := by
          rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  · have := dV.isProb
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure dV.μ
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM x₀)
    have hpt : ∀ y, ptNormSq W n s y ≤ M ^ 2 := fun y => by
      have h1 := Real.sq_sqrt (ptNormSq_nonneg W n s y)
      have h2 := hM y
      nlinarith [Real.sqrt_nonneg (ptNormSq W n s y)]
    have hl2 : sectionL2NormSq W dV n s ≤ M ^ 2 := by
      calc sectionL2NormSq W dV n s ≤ ∫ _ : X, M ^ 2 ∂dV.μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => ptNormSq_nonneg W n s y)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = M ^ 2 := by simp
    calc Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hl2
      _ = M := Real.sqrt_sq hM0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem NoetherProjection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof

theorem RootsLiftToZeros.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof

theorem FiniteSeparatingModel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof NoetherProjection.full RootsLiftToZeros.full

theorem RootsNear.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof

theorem RootsBounded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof

theorem PolyNonvanishDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof

theorem RatPrimeDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof FiniteSeparatingModel.full RootsNear.full RootsBounded.full PolyNonvanishDense.full

theorem NonvanishingDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof RatPrimeDense.full

theorem AnResNullForm.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.proof NonvanishingDense.full

theorem BergmanDensChartSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.proof

theorem BergmanDensIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.proof

theorem BergmanIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.proof

theorem BetaSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BetaSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BetaSum.proof

theorem BirationalCoordinates.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates.proof

theorem BirationalModelExists.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof

theorem HilbFnValueSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.proof

theorem BlockBirationalHilbert.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.proof HilbFnValueSpan.full

theorem BlockChiCovolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.proof

theorem BlockGraphFibreRatio.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.proof

theorem BlockGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.proof

theorem BlockImageArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.proof

theorem EventualPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof

theorem MultigradedHilbertPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof EventualPolynomial.full

theorem GenericFibreVar.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.proof

theorem Closed.FieldNumbers.HilbEventuallyPoly : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.full

theorem GenFibreHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.proof

theorem BlockImageHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.proof

theorem PolySandwich.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.proof

theorem BlockImageGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.proof MultigradedHilbertPolynomial.full GenericFibreVar.full Closed.FieldNumbers.HilbEventuallyPoly GenFibreHomog.full BlockImageHilb.full BlockBirationalHilbert.full PolySandwich.full

theorem BlockImageMetrics.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.proof

theorem PolydiscSubmean.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.proof

theorem ChartTaylorCover.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.proof

theorem UniformBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.proof PolydiscSubmean.full ChartTaylorCover.full

theorem SupNormAgainstL2.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.proof UniformBergmanBound.full

theorem ResolutionPullback.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.proof

theorem SupBoundBlock.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.proof SupNormAgainstL2.full ResolutionPullback.full NonvanishingDense.full

theorem BlockMeasureChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.proof SupBoundBlock.full

theorem BlockResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.proof NonvanishingDense.full

theorem BlockResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.proof

theorem BlockResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.proof BergmanDensChartSum.full

theorem RankOfSections.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.RankOfSections.closed

theorem GenericFibre.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.proof

theorem SectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.proof

theorem BlockSectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.proof RankOfSections.full GenericFibre.full SectionsRank.full BlockImageArith.full BlockImageGenDeg.full

theorem ComplexTaylorTwo.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexTaylorTwo.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexTaylorTwo.proof

theorem ChartBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartBergmanBound.proof PolydiscSubmean.full ComplexTaylorTwo.full

theorem ChartConstantsDetermined.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof

theorem ChartDenominator.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.proof

theorem ChartSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.proof

theorem GramChiDerivative.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.proof

theorem MetricChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.proof GramChiDerivative.full BergmanIntegrable.full BergmanDensIntegrable.full UniformBergmanBound.full BergmanL1Convergence.full

theorem ResolutionImageSup.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.proof ChartSupBound.full

theorem ResolutionSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.proof ResolutionImageSup.full NonvanishingDense.full

theorem ProjFrameBasePtFree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.proof

theorem ResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.proof BergmanDensChartSum.full

theorem ResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.proof NonvanishingDense.full

theorem ConjIntNum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum.proof

theorem ConstantShift.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof

theorem ConstantsDescend.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof

theorem ConstantsRegular.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof ConstantsDescend.full ChartConstantsDetermined.full

theorem CoordArithOfFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof

theorem CovolumeLeGram.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CovolumeLeGram.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CovolumeLeGram.proof

theorem CurvePointsFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CurvePointsFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CurvePointsFinite.proof

theorem ResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.proof

theorem DegLTGrowth.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DegLTGrowth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DegLTGrowth.proof

theorem DegreePositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive.proof

theorem DoubleComplexVanish.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.proof

theorem EmbeddingWeight.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof

theorem EventualPolyLine.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.proof

theorem FibreRelLift.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.proof

theorem FiltrationHilbSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum.proof

theorem G1.full : GroundTheory.Heights₂.Heights.HilbertSamuel.G1.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.G1.proof

theorem SecEq.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CondStatement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof SecEq.full

theorem RelSectionsLarge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelSectionsLarge.Statement :=
  GroundTheory.Heights₂.Heights.Targets.RelSectionsLarge.full

theorem SuccessiveMinimaSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaSpan.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SuccessiveMinimaSpan.of_leaves Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond RelSectionsLarge.full

theorem SegrePrime.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.proof

theorem SegreHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.proof

theorem SegreDimGe.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.proof

theorem MultiDegreePositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.proof SegrePrime.full SegreHilb.full SegreDimGe.full

theorem GenDegAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.proof GenericFibreVar.full MultiDegreePositive.full

theorem GenDegMatAct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.proof

theorem GenOnFibres.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.proof

theorem GeneratedOne.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedOne.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedOne.proof

theorem GeneratedRestrict.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.proof

theorem GeneratedEffectiveSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.proof

theorem GeneratedProductNonneg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.proof GeneratedRestrict.full GeneratedEffectiveSection.full

theorem GeneratedMixedNonneg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedMixedNonneg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedMixedNonneg.proof GeneratedProductNonneg.full

theorem GenDegTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegTwist.proof GenOnFibres.full GenericFibreVar.full GeneratedOne.full GeneratedMixedNonneg.full

theorem QuotPartGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.proof

theorem GenerationOfH1GenAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.proof QuotPartGraded.full

theorem GenTwistGenerated.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.proof

theorem GeneratedNonzeroSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.proof

theorem GeneratedPow.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.proof

theorem GradedSubquot.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.proof

theorem GramContraction.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GramContraction.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GramContraction.proof

theorem GraphIsometric.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric.proof

theorem GraphIsometricForms.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.proof

theorem GridSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GridSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GridSum.proof

theorem Had.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Had.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Had.proof

theorem Halving.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Halving.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Halving.proof

theorem HilbertDimZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertDimZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertDimZero.proof

theorem IntersectionRecursion.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntersectionRecursion.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntersectionRecursion.proof

theorem HilbertIncrement.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement.proof IntersectionRecursion.full

theorem MultigradedFiltration.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.proof

theorem ModulesFromPrimes.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulesFromPrimes.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ModulesFromPrimes.proof MultigradedFiltration.full FiltrationHilbSum.full DegLTGrowth.full

theorem HilbertPrime.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertPrime.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.hilbertPrime

theorem HilbertModule.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertModule.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertModule.proof ModulesFromPrimes.full HilbertPrime.full

theorem HyperplaneRegularSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.proof

theorem IntNumComponents.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntNumComponents.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntNumComponents.proof

theorem IntegralAgainstPositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.proof

theorem IntegralOfBergman.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralOfBergman.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralOfBergman.proof

theorem L1Convergence.full : GroundTheory.Heights₂.Heights.HilbertSamuel.L1Convergence.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.L1Convergence.proof

theorem L2GramLattice.full : GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.proof

theorem LatticeCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeCount.proof

theorem LiftBirationalAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.proof GeneratedNonzeroSection.full

theorem LiftSpread.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.proof

theorem LocalBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LocalBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LocalBergmanBound.proof ChartBergmanBound.full

theorem LocalRep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof

theorem LogDetDerivative.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.proof

theorem MetricTransportSmooth.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.proof

theorem MinkowskiCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount.proof

theorem MixedNumberPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.mixedNumber

theorem PolyNonnegAtZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.proof

theorem MixedTopAlgebra.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.proof PolyNonnegAtZero.full

theorem NefOnGenericOfSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof

theorem NmSectionsFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond

theorem NmSectionsRankBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.proof NmSectionsFinite.full SecMRankBound.full

theorem Packing.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Packing.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Packing.proof

theorem PerturbMonomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.proof GenDegAmple.full

theorem PerturbSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.proof

theorem PointHeightFS.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.proof

theorem ProjDegGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjDegGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ProjDegGenDeg.proof

theorem ProjFrameFibrePt.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.proof

theorem ProjFrameGenPtRel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.proof

theorem ProjFrameGenPtTransc.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.proof

theorem TranscRatioDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.proof

theorem RatioFieldDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.proof

theorem ProjFrameFibreDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.proof ProjFrameFibrePt.full ProjFrameGenPtRel.full ProjFrameGenPtTransc.full TranscRatioDeg.full RatioFieldDeg.full

theorem ProjFrameImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.proof

theorem RatNoetherFrame.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.proof

theorem ReductionComplex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.proof

theorem RelChartPoly.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelChartPoly.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelChartPoly.proof

theorem RelLatticeFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.proof RelSectionsLarge.full

theorem RelTorsionBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelTorsionBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelTorsionBound.proof

theorem RelOneStep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelOneStep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelOneStep.proof RelChartPoly.full RelTorsionBound.full

theorem ResVolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.proof

theorem RootGridLower.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootGridLower.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootGridLower.proof

theorem ScaledFSHProps.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.proof

theorem SecCochReduce.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.proof

theorem SectionBounded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.proof

theorem SectionBoundedMul.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.proof

theorem SectionOrderAtPoint.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.proof

theorem SectionPointValue.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.proof

theorem SectionProduct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.proof

theorem SpanStepLocal.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.proof RelLatticeFinite.full

theorem SpanStepHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.proof SpanStepLocal.full

theorem SerreGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.proof

theorem SectionSpanStep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.proof SpanStepHomog.full SerreGraded.full

theorem SectionSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.proof

theorem SectionsDimZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.proof

theorem SemiampleNef.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SemiampleNef.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SemiampleNef.proof

theorem SemiposTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SemiposTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SemiposTwist.proof

theorem ShiftDegreePolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.proof MixedNumberPolynomial.full

theorem ShiftIntersectionPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.proof

theorem SmallBallVolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallBallVolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallBallVolume.proof

theorem SmallGenTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallGenTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallGenTwist.proof

theorem SmallSectionPointHeight.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.proof SectionOrderAtPoint.full

theorem SpanningExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanningExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanningExtension.proof

theorem SublatticeDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeDegree.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SublatticeDegree.full

theorem SublatticeExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeExtension.proof

theorem SupBoundCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.proof

theorem TopConstantTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof

theorem TwoBlockFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.proof

theorem TwoBlockHorizDiv.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.proof

theorem TwoBlockCoeffCycle.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.proof CoordArithOfFnField.full TwoBlockFnField.full TwoBlockHorizDiv.full

theorem TwoBlockCycleExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.proof

theorem TwoBlockStepBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.proof RankOfSections.full

theorem UnitApprox.full : GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof

theorem VeroneseArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.proof

theorem VeroneseGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.proof

theorem VeroneseGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.proof

theorem VeroneseResolution.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.proof

theorem VeroneseSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.proof

theorem ZCombExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.proof

theorem ZCombLimit.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ZCombLimit.proof

theorem ZeroCocycleSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.proof

theorem Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement :=
  GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite : ReciprocityTheory.ChartRestriction.G.Geo.FibreFiniteStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite

theorem Closed.Inter.regularityPointsSum_holds : GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.proof

theorem Closed.Inter.regularityEmbedding_holds : GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.proof

theorem Closed.FieldNumbers.LocalizedQuotientLength : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof

theorem Closed.Inter.regularityLocalFlat_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.proof

theorem Closed.Inter.regularityDehomogenization_holds : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.proof Closed.FieldNumbers.LocalizedQuotientLength Closed.Inter.regularityLocalFlat_holds

theorem Closed.Inter.LocRingFrac : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingFrac.proof

theorem Closed.Inter.LocRingLocal : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingLocal.proof Closed.Inter.LocRingFrac

theorem Closed.Inter.LocRingNoeth : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.proof Closed.Inter.LocRingFrac

theorem Closed.Inter.LocRingPow : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingPow.proof

theorem Closed.Inter.regularityLocalDimension_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.proof Closed.Inter.LocRingFrac Closed.Inter.LocRingLocal Closed.Inter.LocRingNoeth Closed.Inter.LocRingPow

theorem Closed.Inter.regularityLocalResidue_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.proof

theorem Closed.Inter.regularityLocalCardinality_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.proof Closed.Inter.regularityLocalDimension_holds Closed.Inter.regularityLocalResidue_holds

theorem Closed.PtsSumMeasurable : GroundTheory.Heights₂.Heights.PtsSumMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.PtsSumMeasurable.proof

theorem Closed.Inter.SwapCycles : GroundTheory.Heights₂.Heights.Inter.SwapCycles.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SwapCycles.full

theorem Closed.Inter.GeoNumCut : GroundTheory.Heights₂.Heights.Inter.GeoNumCut.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full

theorem Closed.Inter.TorusInvLevi : GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.Statement :=
  GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof

theorem Closed.Inter.SemiPosTwist : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof Closed.Inter.TorusInvLevi

theorem Closed.SegrePartition : GroundTheory.Heights₂.Heights.SegrePartition.Statement :=
  GroundTheory.Heights₂.Heights.SegrePartition.proof

theorem Closed.SegreChartDim : GroundTheory.Heights₂.Heights.SegreChartDim.Statement :=
  GroundTheory.Heights₂.Heights.SegreChartDim.proof

theorem Closed.SegreCoordGoodProj : GroundTheory.Heights₂.Heights.SegreCoordGoodProj.Statement :=
  GroundTheory.Heights₂.Heights.SegreCoordGoodProj.proof

theorem Closed.ComplexSets.DiscriminantCover : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full

theorem Closed.TubeCollarCompare : GroundTheory.Heights₂.Heights.TubeCollarCompare.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarCompare.proof

theorem Closed.SheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement :=
  GroundTheory.Heights₂.Heights.SheetImageAreaSet.proof

theorem Closed.ChartMassCompare : GroundTheory.Heights₂.Heights.ChartMassCompare.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompare.of_open Closed.SheetImageAreaSet

theorem Closed.MassFinite : GroundTheory.Heights₂.Heights.MassFinite.Statement :=
  GroundTheory.Heights₂.Heights.MassFinite.full

theorem Closed.TubeCollarMass : GroundTheory.Heights₂.Heights.TubeCollarMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarMass.proof Closed.TubeCollarCompare Closed.ChartMassCompare Closed.MassFinite

theorem Closed.TubeDeepWeightMass : GroundTheory.Heights₂.Heights.TubeDeepWeightMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeDeepWeightMass.proof

theorem Closed.ChartMassCompact : GroundTheory.Heights₂.Heights.ChartMassCompact.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompact.of_open Closed.SheetImageAreaSet

theorem Closed.CutOffBoundaryBound : GroundTheory.Heights₂.Heights.CutOffBoundaryBound.Statement :=
  GroundTheory.Heights₂.Heights.CutOffBoundaryBound.of_open Closed.SheetImageAreaSet

theorem Closed.Inter.SheetHessPSD : GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.proof

theorem Closed.Inter.RegCurvBound : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegCurvBound.proof Closed.Inter.TorusInvLevi

theorem Closed.Inter.HorizNotMem : GroundTheory.Heights₂.Heights.Inter.HorizNotMem.Statement :=
  GroundTheory.Heights₂.Heights.Inter.HorizNotMem.proof

theorem Closed.Inter.RatioAlgDep : GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.proof

theorem Closed.Inter.pointFormRank_holds : GroundTheory.Heights₂.Heights.Inter.pointFormRank_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointFormRank_holds.proof Closed.Inter.RatioAlgDep

theorem Closed.Inter.pointFormEuler_holds : GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.proof

theorem Closed.Inter.pointForm_holds : GroundTheory.Heights₂.Heights.Inter.pointForm_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointForm_holds.proof Closed.Inter.pointFormRank_holds Closed.Inter.pointFormEuler_holds

theorem Closed.Inter.PFIntZero : GroundTheory.Heights₂.Heights.Inter.PFIntZero.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFIntZero.proof Closed.Inter.pointFormRank_holds

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoordStatement :=
  GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof

theorem Closed.Inter.BlockRatioAlg : GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.proof

theorem Closed.Inter.BlockGenFinite : GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.proof Closed.Inter.BlockRatioAlg

theorem Closed.Inter.FibreIsolFinite : GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.proof

theorem Closed.Inter.ChartRankAdjoin : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.proof

theorem Closed.Inter.pullbackBadImage_holds : GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
