import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectConstZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanFubini
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFubini
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallAverageLinear
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreePos
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAE
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectSymm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstHomog
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormAssoc
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleAdd
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleSmul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleSectionChow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstRename
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerZeroSpec
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInjSet
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaLocal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSmoothLocalGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacComp
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticImplicitChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchContainsNormalPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchesGoodPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchesToGoodPosition
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBrouwerFixedPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartChangeSheetNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntSlice
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenFixed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalBranchedCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalParametrisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormEnergyDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalMaximumPrinciple
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalRiemannExtension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametrisationSheetsConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionInjectiveOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceProductAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceReachesCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBandAbsEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutDecay
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelongCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLelongError
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLevelSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLevelSetSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegCutTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegVarBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntChartChange
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.UnfoldingFormOfMatrix
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameGraphGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end Heights
end Heights₂
end GroundTheory
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem DefectConstStep.proof (h1 : DefectSymm.Statement) (h2 : ProperSymmCycle.Statement)
    (h3 : AdmissibleAE.Statement) (h4 : CycleSectionData.Statement) : DefectConstStep.Statement := by
  intro e hA n δ h Z f u u' hd hu hu'
  have hdu := h4 n e δ Z f u hd hu
  have hdu' := h4 n e δ Z f u' hd hu'
  have rel : ∀ {Y : ProjCycle ℂ n} {g : ℕ} {d : ℕ} {F : MvPolynomial (Fin (g + 1) × Fin n) ℂ},
      IsChowCycleData Y g d F → ∀ W ∈ Y.support, IsRelevant W :=
    fun hY W hW => (hY.prime W hW).isRelevant
  have hae := (h3 n Z (rel hd)).and ((h3 n _ (rel hdu)).and (h3 n _ (rel hdu')))
  obtain ⟨v, hvZ, hvu, hvu'⟩ := hae.exists
  have s1 : IsAdmissible (cycleSection Z v) u := h2 n Z u v hd.prime hu hvZ hvu
  have s2 : IsAdmissible (cycleSection Z v) u' := h2 n Z u' v hd.prime hu' hvZ hvu'
  rw [h1 e hA n δ h Z f u v hd hu hvZ hvu s1, h1 e hA n δ h Z f v u' hd hvZ hu' s2 hvu']

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine measurable_pi_lambda _ fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem CycleSectionData.proof (h1 : CycleSectionChow.Statement) (h2 : DivCyclePrime.Statement)
    (h3 : SpecFirstHomog.Statement) (h4 : SupportCycleSection.Statement) :
    CycleSectionData.Statement := by
  intro n e δ Z f u hZ hu
  refine ⟨?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, hW, hW'W⟩ := (h4 n Z u).2 W' hW'
    exact h2 n W u (hZ.prime W hW) W' hW'W
  · exact h1 n (e + 1) Z f u hZ.prime hZ.chow hu
  · exact h3 n (e + 1) δ f u hZ.homog

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem mem_support_cycleSection_iff {n : ℕ} (Z : ProjCycle ℂ n) (u : Fin n → ℂ)
    (W' : Ideal (MvPolynomial (Fin n) ℂ)) :
    W' ∈ (cycleSection Z u).support ↔ ∃ W ∈ Z.support, W' ∈ (divCycle W u).support := by
  simp only [Finsupp.mem_support_iff, cycleSection, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, not_forall, mul_eq_zero, not_or, exists_prop]
  constructor <;> rintro ⟨W, h⟩ <;> exact ⟨W, by tauto⟩

theorem SupportCycleSection.proof : SupportCycleSection.Statement := by
  intro n Z u
  refine ⟨fun W hW W' hW' => (mem_support_cycleSection_iff Z u W').mpr ⟨W, hW, hW'⟩,
    fun W' hW' => (mem_support_cycleSection_iff Z u W').mp hW'⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem cycleIntegral_eq_sum {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := rfl

theorem CycleIntegralSection.proof : CycleIntegralSection.Statement := by
  intro n h Z u e g
  rw [cycleIntegral_eq_sum, cycleSection,
    ← Finsupp.sum_finsetSum_index (by intro W; simp) (by intro W a b; push_cast; ring)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.sum_smul_index' (by intro W'; simp), cycleIntegral_eq_sum, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun W' _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChowCycleSwap.proof : ChowCycleSwap.Statement := by
  intro F _ n k Z f hf τ
  obtain ⟨c, -, g, hg, rfl⟩ := hf
  have hex : ∀ W, ∃ d : F, W ∈ Z.support →
      d ^ 2 = 1 ∧ rename (Prod.map τ id) (g W) = C d * g W := by
    intro W
    by_cases hW : W ∈ Z.support
    · obtain ⟨d, hd2, hdg⟩ := chowFormSwap F n k W (g W) (hg W hW) τ
      exact ⟨d, fun _ => ⟨hd2, hdg⟩⟩
    · exact ⟨1, fun h => absurd h hW⟩
  choose d hd using hex
  refine ⟨∏ W ∈ Z.support, d W ^ Z W, ?_, ?_⟩
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun W hW => ?_
    rw [← pow_mul, mul_comm, pow_mul, (hd W hW).1, one_pow]
  · rw [map_mul, rename_C, map_prod]
    rw [Finset.prod_congr rfl fun W hW => by
      rw [map_pow, (hd W hW).2, mul_pow, ← C_pow]]
    rw [Finset.prod_mul_distrib, map_prod C]
    ring

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem mahler_C_mul_of_norm_eq_one {n k : ℕ} (h : HermNorm n) (c : ℂ) (hc : ‖c‖ = 1)
    (g : MvPolynomial (Fin k × Fin n) ℂ) : mahler h k (C c * g) = mahler h k g := by
  have hfun : (fun v : Fin k × Fin n → ℂ => Real.log ‖eval v (C c * g)‖) =
      fun v => Real.log ‖eval v g‖ := by
    funext v
    rw [eval_mul, eval_C, norm_mul, hc, one_mul]
  unfold mahler
  rw [hfun]

theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

theorem SpecFirstSwapMahler.proof (h1 : SpecFirstRename.Statement) (h2 : ChowCycleSwap.Statement) :
    SpecFirstSwapMahler.Statement := by
  intro n e h Z f u u' hf
  obtain ⟨c, hc2, hren⟩ := h2 ℂ n (e + 1 + 1) Z f hf (Equiv.swap 0 1)
  have hc : ‖c‖ = 1 := by
    have hsq : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc2, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hsq
  have key : specFirst (specFirst f u) u' = C c * specFirst (specFirst f u') u := by
    rw [← h1 n e f u' u, hren, specFirst_C_mul, specFirst_C_mul]
  rw [key, mahler_C_mul_of_norm_eq_one h c hc]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ProperSymmCycle.proof (h1 : ProperSymm.Statement) (h2 : SupportCycleSection.Statement) :
    ProperSymmCycle.Statement := by
  intro n Z u u' hprime hu hu' hadm W'' hW''
  obtain ⟨W, hW, hW''W⟩ := (h2 n Z u').2 W'' hW''
  have hadmW : IsAdmissible (divCycle W u) u' := fun W' hW' =>
    hadm W' ((h2 n Z u).1 W hW hW')
  exact h1 n W u u' (hprime W hW) (hu W hW) (hu' W hW) hadmW W'' hW''W

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem MahlerSection.proof (h₁ : MahlerSectionOfConst.Statement) (h₂ : DefectConstZero.Statement)
    (h₃ : DefectConstStep.Statement) : MahlerSection.Statement := by
  have hdim : ∀ e, MahlerSectionDim e := by
    intro e
    induction e with
    | zero => exact h₁ 0 h₂
    | succ e ih => exact h₁ (e + 1) (h₃ e ih)
  intro n e δ h Z f u hprime hchow hhom hadm
  exact hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ConeKrullDimLe.proof (hDim : ConeFiniteFibreDim.Statement) : ConeKrullDimLe.Statement :=
  fun n m h J hJ hm hmn hae => hDim n m h J hJ hm hmn hae

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjPrimeHasPoint.proof : ProjPrimeHasPoint.Statement := by
  intro F _ n W hW
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.isRelevant
  by_contra hcon
  push Not at hcon
  apply hj
  have hmem : (X j : MvPolynomial (Fin n) F) ∈
      vanishingIdeal F (zeroLocus (AlgebraicClosure F) W) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨q, hq, hne⟩ := hcon x hx0
      exact absurd (hx q hq) hne
  rwa [IsPrime.vanishingIdeal_zeroLocus] at hmem

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ChowFormBaseChange.full : ChowFormBaseChange.Statement :=
  (ChowFormBaseChange.proof
    RadicalBaseChange.proof
    (ChowFormExtend.proof RadicalBaseChange.proof)
    (ChowFormReduced.proof_of_prime_separate
      IncIdealPrime.full
      (IncIdealSeparate.proof
        IncidenceZeroLocus.proof
        (FormsThroughPoint.proof
          IncidenceZeroLocus.proof
          ThroughPointIncIdeal.proof
          (ChartZeroTrdeg.proof AffineChartTrdeg.full)
          (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof)
          TrdegBaseAlgebraic.proof)
        (IncIdealNeBotDim.proof IncIdealDim.full))))

theorem BaseChangeAvoid.full : BaseChangeAvoid.Statement :=
  BaseChangeAvoid.proof

theorem ProjPrimeHasPoint.full : ProjPrimeHasPoint.Statement :=
  ProjPrimeHasPoint.proof

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  Vertical.ChowFormSectionVertical.full

theorem ConeMassOfFibre.full : ConeMassOfFibre.Statement :=
  (ConeMassOfFibre.of_open
    ConeFiniteFibreDim.proof
    (ConeGraphCover.proof
      ConeFiniteFibreDim.proof
      (ConeTangentDim.proof
        (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
        NullSmaller.full
        (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
      (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof))
    (ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof)
    (ConeTangentDim.proof
      (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
      NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (GraphAreaFibre.proof
      (GraphAreaIntegral.proof GraphAreaHolomorphic.full)
      TangentJacComp.proof
      AreaMultiplicityWeight.proof)
    TangentGaussInvariant.proof)

theorem ConeIntegralMass.full : ConeIntegralMass.Statement :=
  (ConeIntegralMass.proof ConeFibreDegree.full ConeMassOfFibre.full)

theorem ConeBallFinite.full : ConeBallFinite.Statement :=
  (ConeBallFinite.proof ConeIntegralMass.full)

theorem ConeFsLogIntegrable.full : ConeFsLogIntegrable.Statement :=
  (ConeFsLogIntegrable.proof ConeBallFinite.full ConeSlabBound.full)

theorem ConeLogBound.full : ConeLogBound.Statement :=
  (ConeLogBound.of_leaves
    ConeIntegralMass.full
    ConeBallFinite.full
    ConeFsLogIntegrable.full
    ConeHyperplaneNull.full)

theorem BaseChangeLogBound.full : BaseChangeLogBound.Statement :=
  (BaseChangeLogBound.of_leaves
    ChowFormBaseChange.full
    BaseChangeAvoid.full
    ConeIntegralMass.full
    ConeBallFinite.full
    ConeFsLogIntegrable.full
    ConeHyperplaneNull.full)

theorem GreenSymmetry.of_remaining
    (hChowFormSectionAlgClosed : ChowFormSectionAlgClosed.Statement)
    (hSliceMassFinite : SliceMassFinite.Statement)
    (hChartChangeLocal : ChartChangeLocal.Statement)
    (hDivisorOneComponent : DivisorOneComponent.Statement)
    (hDivisorBranches : DivisorBranches.Statement)
    (hBranchIntDecompose : BranchIntDecompose.Statement)
    (hSliceBranchInt : SliceBranchInt.Statement)
    (hPolydiscLelongLimit : PolydiscLelongLimit.Statement)
    (hTwinComplexSetsNormalRiemannExtensionLocal : IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtensionLocal.Statement)
    (hTwinComplexSetsIrreducibleGermProjectionOpenNear : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermProjectionOpenNear.Statement)
    (hTwinComplexSetsProperOpenProjectionBranchLocus : IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionBranchLocus.Statement)
    (hTwinComplexSetsUnbranchedProperCountConstant : IndefiniteRowSideFullHecke.ComplexSets.UnbranchedProperCountConstant.Statement)
    (hTwinComplexSetsUnbranchedFibreSections : IndefiniteRowSideFullHecke.ComplexSets.UnbranchedFibreSections.Statement)
    (hTwinComplexSetsChangeOfVariablesDegree : IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree.Statement)
    (hTwinComplexSetsProperHolomorphicSurjective : IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective.Statement)
    (hTwinComplexSetsHolomorphicKernelFibre : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.Statement)
    (hTwinComplexSetsGenericProjectionFinite : IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement)
    (hTwinComplexSetsLocalOrder : IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement)
    (hRegMassNearSmall : RegMassNearSmall.Statement)
    (hSliceFsLogIntegrable : SliceFsLogIntegrable.Statement)
    (hSliceTubeBandAbsEnergy : SliceTubeBandAbsEnergy.Statement) :
    GreenSymmetry.Statement := by
  have hComplexSetsLinearNoetherNormalization : ComplexSets.LinearNoetherNormalization.Statement :=
    ComplexSets.LinearNoetherNormalization.proof
  have hComplexSetsDiscriminantCover : ComplexSets.DiscriminantCover.Statement :=
    HilbertSamuel.Closed.ComplexSets.DiscriminantCover
  have hDiscriminantSheetCover : DiscriminantSheetCover.Statement :=
    DiscriminantSheetCover.proof hComplexSetsDiscriminantCover
  have hConeSliceSheetParam : ConeSliceSheetParam.Statement :=
    ConeSliceSheetParam.proof hDiscriminantSheetCover
  have hAreaFormulaLocal : AreaFormulaLocal.Statement :=
    AreaFormulaLocal.proof
  have hAreaFormulaInjSet : AreaFormulaInjSet.Statement :=
    AreaFormulaInjSet.proof hAreaFormulaLocal
  have hAreaFormulaInj : AreaFormulaInj.Statement :=
    AreaFormulaInj.proof hAreaFormulaInjSet
  have hConeMapAreaOne : ConeMapAreaOne.Statement :=
    ConeMapAreaOne.proof hAreaFormulaInj
  have hConeMapArea : ConeMapArea.Statement :=
    ConeMapArea.proof hConeMapAreaOne
  have hConeSheetGramLintegral : ConeSheetGramLintegral.Statement :=
    ConeSheetGramLintegral.proof hConeSliceSheetParam hConeMapArea
  have hSliceIdeal : SliceIdeal.Statement :=
    SliceIdeal.full
  have hSheetFormCompare : SheetFormCompare.Statement :=
    SheetFormCompare.proof
  have hSliceFormMass : SliceFormMass.Statement :=
    SliceFormMass.proof hSliceIdeal hSliceMassFinite hSheetFormCompare
  have hTwinComplexSetsFiniteMapOpen : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full
  have hTwinComplexSetsCriticalImageNull : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full
  have hChartChangeSheetNull : ChartChangeSheetNull.Statement :=
    ChartChangeSheetNull.proof hTwinComplexSetsFiniteMapOpen hTwinComplexSetsCriticalImageNull
  have hVarIntChartChange : VarIntChartChange.Statement :=
    VarIntChartChange.proof hComplexSetsLinearNoetherNormalization hChartChangeSheetNull
      hChartChangeLocal
  have hFormIntSlice : FormIntSlice.Statement :=
    FormIntSlice.proof hSliceIdeal hSliceFormMass hVarIntChartChange
  have hSheetImageAreaSet : SheetImageAreaSet.Statement :=
    HilbertSamuel.Closed.SheetImageAreaSet
  have hLelongLimitOffZero : LelongLimitOffZero.Statement :=
    LelongLimitOffZero.of_open hSheetImageAreaSet
  have hDivisorGeneralPointBranches : DivisorGeneralPointBranches.Statement :=
    DivisorGeneralPointBranches.proof hDivisorOneComponent hDivisorBranches
  have hTwinComplexSetsNormalModelExists : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
  have hTwinComplexSetsNormalModelProper : IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof
  have hTwinComplexSetsRiemannExtensionAnalytic : IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof
  have hTwinComplexSetsHolomorphicFibreInfinite : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof
  have hTwinComplexSetsBranchOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof hTwinComplexSetsHolomorphicFibreInfinite
  have hTwinComplexSetsVanishNearPoint : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full
  have hJacobianRankGeneric : JacobianRankGeneric.Statement :=
    JacobianRankGeneric.proof
  have hConormalGenerationGeneric : ConormalGenerationGeneric.Statement :=
    ConormalGenerationGeneric.proof
  have hFrameJacobianGeneric : FrameJacobianGeneric.Statement :=
    FrameJacobianGeneric.proof hJacobianRankGeneric hConormalGenerationGeneric
  have hFrameImplicitGraph : FrameImplicitGraph.Statement :=
    FrameImplicitGraph.proof
  have hFrameGraphGeneric : FrameGraphGeneric.Statement :=
    FrameGraphGeneric.proof hFrameJacobianGeneric hFrameImplicitGraph
  have hTwinComplexSetsRegularOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.proof hFrameGraphGeneric
  have hTwinComplexSetsRegularLocusIdentity : IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.proof hTwinComplexSetsRegularOffHypersurface
  have hTwinComplexSetsNormalGermIrreducible : IndefiniteRowSideFullHecke.ComplexSets.NormalGermIrreducible.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalGermIrreducible.proof hTwinComplexSetsRegularLocusIdentity
      hTwinComplexSetsNormalRiemannExtensionLocal hTwinComplexSetsVanishNearPoint
  have hTwinComplexSetsAnalyticImplicitChart : IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof
  have hTwinComplexSetsRegularLocusDense : IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.proof hTwinComplexSetsAnalyticImplicitChart
  have hTwinComplexSetsGermFiniteProjection : IndefiniteRowSideFullHecke.ComplexSets.GermFiniteProjection.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.GermFiniteProjection.proof
  have hTwinComplexSetsProperOpenProjectionCover : IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionCover.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionCover.proof hTwinComplexSetsProperOpenProjectionBranchLocus
      hTwinComplexSetsUnbranchedProperCountConstant
  have hTwinComplexSetsFiniteGermProjectionCover : IndefiniteRowSideFullHecke.ComplexSets.FiniteGermProjectionCover.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.FiniteGermProjectionCover.proof
      hTwinComplexSetsIrreducibleGermProjectionOpenNear hTwinComplexSetsProperOpenProjectionCover
  have hTwinComplexSetsLocalParametrisation : IndefiniteRowSideFullHecke.ComplexSets.LocalParametrisation.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalParametrisation.proof hTwinComplexSetsGermFiniteProjection
      hTwinComplexSetsFiniteGermProjectionCover
  have hTwinComplexSetsSheetPieceProductAnalytic : IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.proof hTwinComplexSetsUnbranchedFibreSections
  have hTwinComplexSetsSheetPieceReachesCentre : IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.proof
  have hTwinComplexSetsParametrisationSheetsConnected : IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.proof hTwinComplexSetsSheetPieceProductAnalytic
      hTwinComplexSetsSheetPieceReachesCentre
  have hTwinComplexSetsIrreducibleGermRegularConnected : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermRegularConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermRegularConnected.proof hTwinComplexSetsLocalParametrisation
      hTwinComplexSetsParametrisationSheetsConnected
  have hTwinComplexSetsManifoldZerosComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.proof
  have hTwinComplexSetsIrreducibleGermComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermComplementConnected.proof hTwinComplexSetsRegularLocusDense
      hTwinComplexSetsIrreducibleGermRegularConnected
      hTwinComplexSetsManifoldZerosComplementConnected
  have hTwinComplexSetsNormalComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.NormalComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalComplementConnected.proof hTwinComplexSetsVanishNearPoint
      hTwinComplexSetsNormalGermIrreducible hTwinComplexSetsIrreducibleGermComplementConnected
  have hTwinComplexSetsNormalLocallyIrreducible : IndefiniteRowSideFullHecke.ComplexSets.NormalLocallyIrreducible.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalLocallyIrreducible.proof hTwinComplexSetsVanishNearPoint
      hTwinComplexSetsNormalComplementConnected
  have hTwinComplexSetsBrouwerFixedPoint : IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.proof hTwinComplexSetsChangeOfVariablesDegree
  have hTwinComplexSetsInvarianceOfDomain : IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.proof hTwinComplexSetsBrouwerFixedPoint
  have hTwinComplexSetsInjectiveHolomorphicOpen : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.proof hTwinComplexSetsInvarianceOfDomain
  have hTwinComplexSetsNormalModelOpenMapping : IndefiniteRowSideFullHecke.ComplexSets.NormalModelOpenMapping.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelOpenMapping.proof hTwinComplexSetsNormalLocallyIrreducible
      hTwinComplexSetsBranchOffHypersurface hTwinComplexSetsInjectiveHolomorphicOpen
  have hTwinComplexSetsBranchLift : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchLift.proof hTwinComplexSetsRiemannExtensionAnalytic
      hTwinComplexSetsBranchOffHypersurface hTwinComplexSetsNormalModelOpenMapping
      hTwinComplexSetsNormalModelProper
  have hTwinComplexSetsBranchFillDimension : IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof hTwinComplexSetsHolomorphicFibreInfinite
  have hComplexSetsFibreBound : ComplexSets.FibreBound.Statement :=
    ComplexSets.FibreBound.full
  have hTwinComplexSetsHolomorphicIsolatedFibreOpen : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicIsolatedFibreOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.HolomorphicIsolatedFibreOpen.proof hTwinComplexSetsProperHolomorphicSurjective
  have hTwinComplexSetsNormalOpenMapping : IndefiniteRowSideFullHecke.ComplexSets.NormalOpenMapping.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalOpenMapping.proof hTwinComplexSetsNormalLocallyIrreducible
      hComplexSetsLinearNoetherNormalization hComplexSetsFibreBound hComplexSetsDiscriminantCover
      hTwinComplexSetsHolomorphicIsolatedFibreOpen
  have hTwinComplexSetsCriticalFlatNotInjective : IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  have hTwinComplexSetsInjectiveHolomorphicJacobianNeZero : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof hTwinComplexSetsHolomorphicKernelFibre
      hTwinComplexSetsCriticalFlatNotInjective
  have hTwinComplexSetsInjectiveHolomorphicInverse : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof
      hTwinComplexSetsInjectiveHolomorphicJacobianNeZero
  have hTwinComplexSetsProjectionInjectiveOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.proof_of_rank hJacobianRankGeneric
      hConormalGenerationGeneric
  have hTwinComplexSetsBranchInverseOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.proof hTwinComplexSetsInjectiveHolomorphicInverse
      hTwinComplexSetsProjectionInjectiveOffHypersurface
  have hTwinComplexSetsNormalRiemannExtension : IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtension.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtension.proof hTwinComplexSetsNormalRiemannExtensionLocal
      hTwinComplexSetsNormalLocallyIrreducible
  have hTwinComplexSetsBranchInverseHolomorphic : IndefiniteRowSideFullHecke.ComplexSets.BranchInverseHolomorphic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchInverseHolomorphic.proof hTwinComplexSetsBranchFillDimension
      hTwinComplexSetsNormalOpenMapping hTwinComplexSetsBranchInverseOffHypersurface
      hTwinComplexSetsNormalRiemannExtension hTwinComplexSetsNormalLocallyIrreducible
  have hTwinComplexSetsIsolatedFibreOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof hTwinComplexSetsGenericProjectionFinite
      hTwinComplexSetsFiniteMapOpen
  have hTwinComplexSetsLocalBranchedCovering : IndefiniteRowSideFullHecke.ComplexSets.LocalBranchedCovering.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalBranchedCovering.proof hDiscriminantSheetCover
      hTwinComplexSetsIsolatedFibreOpen
  have hTwinComplexSetsLocalTrace : IndefiniteRowSideFullHecke.ComplexSets.LocalTrace.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalTrace.proof hTwinComplexSetsLocalBranchedCovering
  have hTwinComplexSetsNormalMaximumPrinciple : IndefiniteRowSideFullHecke.ComplexSets.NormalMaximumPrinciple.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalMaximumPrinciple.proof hTwinComplexSetsLocalTrace
  have hTwinComplexSetsBranchContainsNormalPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchContainsNormalPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchContainsNormalPoint.proof hTwinComplexSetsNormalLocallyIrreducible
      hTwinComplexSetsBranchInverseHolomorphic hTwinComplexSetsNormalRiemannExtension
      hTwinComplexSetsNormalMaximumPrinciple
  have hTwinComplexSetsBranchAwayFromRim : IndefiniteRowSideFullHecke.ComplexSets.BranchAwayFromRim.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchAwayFromRim.proof hTwinComplexSetsNormalModelExists
      hTwinComplexSetsNormalModelProper hTwinComplexSetsBranchLift
      hTwinComplexSetsNormalLocallyIrreducible hTwinComplexSetsBranchContainsNormalPoint
  have hTwinComplexSetsBranchProperAtPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.proof hTwinComplexSetsBranchAwayFromRim
  have hLelongLimitAtBranches : LelongLimitAtBranches.Statement :=
    LelongLimitAtBranches.proof hBranchIntDecompose hSliceBranchInt hPolydiscLelongLimit
      hTwinComplexSetsBranchProperAtPoint
  have hTwinComplexSetsGeneralProjection : IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.full
  have hTwinComplexSetsOneComponentGeneralPoint : IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.full
  have hTwinComplexSetsSliceImmersiveGeneral : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
  have hTwinComplexSetsBranchesGoodPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchesGoodPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchesGoodPoint.proof hTwinComplexSetsGeneralProjection
      hTwinComplexSetsOneComponentGeneralPoint hTwinComplexSetsSliceImmersiveGeneral
      hTwinComplexSetsBranchProperAtPoint
  have hTwinComplexSetsPowerUnitCount : IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.full
  have hTwinComplexSetsBranchesToGoodPosition : IndefiniteRowSideFullHecke.ComplexSets.BranchesToGoodPosition.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchesToGoodPosition.proof hTwinComplexSetsBranchesGoodPoint
      hTwinComplexSetsPowerUnitCount
  have hLocalOrder : LocalOrder.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.unfolding_form_of_matrix hTwinComplexSetsBranchesToGoodPosition
      hTwinComplexSetsLocalOrder
  have hLelongLimitGoodPoints : LelongLimitGoodPoints.Statement :=
    LelongLimitGoodPoints.proof hDivisorGeneralPointBranches hLelongLimitAtBranches hLocalOrder
  have hChartMassCompact : ChartMassCompact.Statement :=
    HilbertSamuel.Closed.ChartMassCompact
  have hVarMassNearSmall : VarMassNearSmall.Statement :=
    VarMassNearSmall.proof hChartMassCompact
  have hLelongMassNearSmall : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hRegMassNearSmall hVarMassNearSmall
  have hVarIntAdd : VarIntAdd.Statement :=
    VarIntAdd.of_open hSheetImageAreaSet
  have hLelongLimitOnZero : LelongLimitOnZero.Statement :=
    LelongLimitOnZero.proof hLelongLimitOffZero hLelongLimitGoodPoints hLelongMassNearSmall
      hVarIntAdd
  have hSliceBoundaryBound : SliceBoundaryBound.Statement :=
    SliceBoundaryBound.proof hChartMassCompact hSliceFormMass
  have hMaDensChain : MaDensChain.Statement :=
    MaDensChain.proof
  have hTubeCollarMass : TubeCollarMass.Statement :=
    HilbertSamuel.Closed.TubeCollarMass
  have hTubeDeepRankOne : TubeDeepRankOne.Statement :=
    TubeDeepRankOne.proof
  have hIsolatedFibreOpenPoly : IsolatedFibreOpenPoly.Statement :=
    IsolatedFibreOpenPoly.full
  have hComplexSetsGenericProjectionFinite : ComplexSets.GenericProjectionFinite.Statement :=
    ComplexSets.GenericProjectionFinite.full
  have hDominantFibreBound : DominantFibreBound.Statement :=
    DominantFibreBound.proof hComplexSetsGenericProjectionFinite
  have hImageDimLe : ImageDimLe.Statement :=
    ImageDimLe.proof
  have hIsolatedPointsCountPrime : IsolatedPointsCountPrime.Statement :=
    IsolatedPointsCountPrime.proof hIsolatedFibreOpenPoly hDominantFibreBound hImageDimLe
  have hIsolatedPointsCount : IsolatedPointsCount.Statement :=
    IsolatedPointsCount.proof hIsolatedPointsCountPrime
  have hTubeDeepAreaCount : TubeDeepAreaCount.Statement :=
    TubeDeepAreaCount.proof hIsolatedPointsCount
  have hTubeDeepWeightMass : TubeDeepWeightMass.Statement :=
    HilbertSamuel.Closed.TubeDeepWeightMass
  have hTubeDeepMass : TubeDeepMass.Statement :=
    TubeDeepMass.proof hTubeDeepRankOne hTubeDeepAreaCount hTubeDeepWeightMass
  have hTubeEuclMass : TubeEuclMass.Statement :=
    TubeEuclMass.proof hTubeCollarMass hTubeDeepMass
  have hCutOffLimit : CutOffLimit.Statement :=
    CutOffLimit.of_open hSheetImageAreaSet hTubeEuclMass
  have hStokesOnChart : StokesOnChart.Statement :=
    StokesOnChart.proof hComplexSetsDiscriminantCover hCutOffLimit
  have hLogNormGradDensNonneg : LogNormGradDensNonneg.Statement :=
    LogNormGradDensNonneg.proof
  have hSliceLevelSetSmooth : SliceLevelSetSmooth.Statement :=
    SliceLevelSetSmooth.proof hStokesOnChart hLogNormGradDensNonneg hMaDensChain hChartMassCompact
      hSliceMassFinite
  have hSliceLevelSet : SliceLevelSet.Statement :=
    SliceLevelSet.proof hSliceLevelSetSmooth
  have hSliceCutDecay : SliceCutDecay.Statement :=
    SliceCutDecay.proof hMaDensChain hSliceLevelSet hSliceMassFinite
  have hSliceComponents : SliceComponents.Statement :=
    SliceComponents.full
  have hSliceWeightMassFinite : SliceWeightMassFinite.Statement :=
    SliceWeightMassFinite.proof hSliceMassFinite
  have hStokesOnVariety : StokesOnVariety.Statement :=
    StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass
  have hLogIntegrable : LogIntegrable.Statement :=
    LogIntegrable.of_open hSheetImageAreaSet
  have hLelongRegularise : LelongRegularise.Statement :=
    LelongRegularise.of_open hSheetImageAreaSet
  have hLelongLimit : LelongLimit.Statement :=
    LelongLimit.of_open hLelongLimitOnZero hSheetImageAreaSet
  have hPoincareLelong : PoincareLelong.Statement :=
    PoincareLelong.proof hStokesOnVariety hLelongRegularise hLelongLimit
  have hSliceFormLelongCompact : SliceFormLelongCompact.Statement :=
    SliceFormLelongCompact.proof hStokesOnVariety hLogIntegrable hPoincareLelong hChartMassCompact
      hSliceIdeal hSliceComponents
  have hSliceRegVarBound : SliceRegVarBound.Statement :=
    SliceRegVarBound.proof hSliceFormMass
  have hSliceRegMassMono : SliceRegMassMono.Statement :=
    SliceRegMassMono.proof hSliceFormMass
  have hSliceRegMassContinuous : SliceRegMassContinuous.Statement :=
    SliceRegMassContinuous.proof hSliceMassFinite hSheetFormCompare
  have hSliceCutOffLimit : SliceCutOffLimit.Statement :=
    SliceCutOffLimit.of_open hSheetFormCompare hSliceBoundaryBound hSliceCutDecay hSliceMassFinite
  have hSliceCutChain : SliceCutChain.Statement :=
    SliceCutChain.proof hChartMassCompact hLogIntegrable
  have hSliceLogIntegrable : SliceLogIntegrable.Statement :=
    SliceLogIntegrable.proof hSliceFsLogIntegrable
  have hSliceWeightBound : SliceWeightBound.Statement :=
    SliceWeightBound.proof hSliceLogIntegrable
  have hLogNormEnergyDensNonneg : LogNormEnergyDensNonneg.Statement :=
    LogNormEnergyDensNonneg.proof
  have hSliceBandAbsEnergy : SliceBandAbsEnergy.Statement :=
    SliceBandAbsEnergy.proof hLogIntegrable hLogNormEnergyDensNonneg hSliceTubeBandAbsEnergy
  have hSliceBandEnergy : SliceBandEnergy.Statement :=
    SliceBandEnergy.proof hLogIntegrable hLogNormEnergyDensNonneg hSliceBandAbsEnergy
  have hSliceLelongError : SliceLelongError.Statement :=
    SliceLelongError.proof hSliceCutChain hSliceWeightBound hSliceBandEnergy
  have hSliceSectionMass : SliceSectionMass.Statement :=
    SliceSectionMass.of_open hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError
      hSliceMassFinite hTubeEuclMass
  have hSliceRegMassLimit : SliceRegMassLimit.Statement :=
    SliceRegMassLimit.proof hSliceCutOffLimit hStokesOnVariety hSliceFormLelongCompact
      hSliceSectionMass hSliceFormMass hChartMassCompact
  have hSliceSectionTailMass : SliceSectionTailMass.Statement :=
    SliceSectionTailMass.proof hSliceMassFinite
  have hSliceRegCutTail : SliceRegCutTail.Statement :=
    SliceRegCutTail.proof hSliceFormMass
  have hSliceCutTailMass : SliceCutTailMass.Statement :=
    SliceCutTailMass.proof hSliceMassFinite
  have hSliceRegTailMass : SliceRegTailMass.Statement :=
    SliceRegTailMass.proof hSliceRegMassMono hSliceRegMassContinuous hSliceRegMassLimit
      hSliceSectionTailMass hSliceRegCutTail hSliceCutTailMass
  have hSliceRegTail : SliceRegTail.Statement :=
    SliceRegTail.proof hSliceRegVarBound hSliceRegTailMass hSliceCutTailMass
  have hSliceFormLelong : SliceFormLelong.Statement :=
    SliceFormLelong.proof hSliceIdeal hSliceComponents hSliceWeightMassFinite
      hSliceFormLelongCompact hSliceRegTail
  have hGreenSymmetry : GreenSymmetry.Statement :=
    GreenSymmetry.of_open hChowFormSectionAlgClosed hComplexSetsLinearNoetherNormalization
      hConeSheetGramLintegral hFormIntSlice hLelongLimitOnZero hSheetFormCompare hSheetImageAreaSet
      hSliceBoundaryBound hSliceCutDecay hSliceFormLelong hSliceLelongError hSliceMassFinite
      hTubeEuclMass
  exact hGreenSymmetry

end GroundTheory.Heights₂.Heights
end
