import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegreeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentsAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntNumComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResInt
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFrameChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPointHeightFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricToFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FirstPointNeSecondPoint
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDegrees
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsArithVarNoBlocks
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

theorem BlockResolutionDegree.proof (hRank : BlockSectionsRank.Statement)
    (hInt : BlockResolutionDegreeIntegral.Statement) : BlockResolutionDegree.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h₀ h₁ s₀ s₁ t ht
  obtain ⟨C, hC⟩ := hRank D K ι Ω d.y d.k₀ d.one_le d.arith d.birat
  refine ⟨C, fun n => ?_⟩
  rw [hInt D K ι Ω d A₀ A₁ h₀ h₁ s₀ s₁ t ht]
  exact hC n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ClopenDegree.proof (h₁ : ClopenComponents.Statement) (h₂ : ComponentDegree.Statement)
    (h₃ : ComponentsAdditive.Statement) (h₄ : IntNumComponents.Statement) : ClopenDegree.Statement := by
  intro K _ _ ι _ P e L A hP hL hA hcl
  obtain ⟨S, hS, hAS, hI⟩ := h₁ K ι P e A hP hA hcl
  rw [hI, hAS, h₃ K ι P e L S hP hL hS, h₄ K ι P e _ S hP hS]
  push_cast
  exact Finset.sum_congr rfl fun W hW => h₂ K ι P e L W hP hL (hS W hW)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem extC_map_rat_eq_map_complex {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC (P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      P.map (MvPolynomial.map (Int.castRingHom ℂ)) := by
  have hc : (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MvPolynomial (Σ k, ι k) ℂ) :=
    RingHom.ext GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.map_rat_complex
  simp only [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC, ReciprocityTheory.AnForm.R.extC, Ideal.map_map, hc]

theorem ComponentDegree.proof (h₁ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.Statement)
    (h₂ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement) (h₃ : ComponentResInt.Statement) :
    ComponentDegree.Statement := by
  intro K _ _ ι _ P e L W hP hL hW
  have hW' : W ∈ (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.extC
      (P.map (MvPolynomial.map (Int.castRingHom ℚ)))).minimalPrimes := by
    rw [extC_map_rat_eq_map_complex]
    exact hW
  have hV : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IsProjVar W e :=
    GroundTheory.Heights₂.Heights.Inter.BaseChange.isProjVar_of_mem_minimalPrimes
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP) hW'
  have hR := h₂ K ι W e hV
  rw [h₃ K ι P e L W hP hL hW hR]
  exact h₁ K ι W e L hV hR fun j =>
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isSmoothMetric_of_isSmoothHerm W (L j) (hL j)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace FrameChange

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_matAct (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem isInvMat_mul {A A' : Matrix J J ℚ} (hA : IsInvMat A) (hA' : IsInvMat A') : IsInvMat (A * A') := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨C', hC'⟩ := hA'
  refine ⟨C' * C, fun v => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC' (C.mulVec v)).1, (hC v).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC (A'.mulVec v)).2, (hC' v).2]

open Classical in

def scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) : Matrix J J ℚ :=
  Matrix.diagonal fun i => if i ∈ Set.range e then 1 else (m : ℚ)

open Classical in

theorem matAct_scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) (y : J → Ω) :
    matAct (scaleMat e m) y = scaleOff e m y := by
  funext i
  simp only [matAct, scaleMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  rw [if_pos rfl]
  unfold scaleOff
  split_ifs <;> simp

open Classical in

theorem isInvMat_scaleMat {D : ℕ} (e : Fin (D + 1) → J) {m : ℕ} (hm : 0 < m) : IsInvMat (scaleMat e m) := by
  have hc : ∀ i, (if i ∈ Set.range e then 1 else (m : ℚ)) ≠ 0 := fun i => by
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast hm.ne'
  refine ⟨Matrix.diagonal fun i => (if i ∈ Set.range e then 1 else (m : ℚ))⁻¹, fun v => ⟨?_, ?_⟩⟩
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]

end Matrices

theorem proof (hN : RatNoetherFrame.Statement) (hT : HSMTransport.Statement) (hI : ResChiIndex.Statement) :
    FrameChange.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨B₀, e, hB₀, hfr⟩ := hN D Ω κ d.x d.arith
  obtain ⟨m, hm, hfr'⟩ := exists_scaleOff_isProjFrame (matAct B₀ d.x) e hfr
  have hB : IsInvMat (scaleMat e m * B₀) := isInvMat_mul (isInvMat_scaleMat e hm) hB₀
  obtain ⟨d', hx', hm', hG⟩ := hT D Ω κ d _ hB
  have hx'' : d'.x = scaleOff e m (matAct B₀ d.x) := by
    rw [hx', ← matAct_matAct, matAct_scaleMat]
  refine ⟨_, d', e, hB, hx', hm', by rw [hx'']; exact hfr', ?_⟩
  have h0 := hI D Ω κ d d' _ hB hx' hG
  have hz : (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) = fun _ => (0 : ℝ) :=
    funext fun n => by rw [h0 n, sub_self]
  rw [hz]
  exact isLittleO_zero _ _

end FrameChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

theorem eventually_blocks_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ᶠ w in 𝓝 z, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
  refine Filter.eventually_all.2 fun k => ?_
  obtain ⟨i, hi⟩ := hz k
  exact ((continuous_apply (⟨k, i⟩ : Σ k, ι k)).continuousAt.eventually_ne hi).mono fun w hw => ⟨i, hw⟩

theorem leviForm_congr_add_const {N : Type} [Fintype N] {φ ψ : (N → ℂ) → ℝ} {z : N → ℂ} (c : ℝ)
    (h : φ =ᶠ[𝓝 z] fun w => ψ w + c) (w : N → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := by
    have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ :=
      h.fderiv.trans (Eventually.of_forall fun x => fderiv_add_const c)
    exact h1.fderiv_eq
  unfold leviForm
  rw [h2]

theorem SuccessiveMinimaDual.proof (hG1 : G1.Statement) (hW : EmbeddingWeight.Statement)
    (hT : TwistIntersection.Statement) : SuccessiveMinimaDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 II Λ hD hII hvar hbir ha hP0 hsemi hconj hΛ hΛc huniq hmon
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hW K ι Ω F y Λ hΛ hΛc huniq
  have hA' : (A.tensor B).a = fun k => (a k : ℤ) := by
    rw [show (A.tensor B).a = A.a + B.a from rfl, ha, hBa, add_zero]
  have hsemi' : IsSemipositiveRel P0 (mCoordIdeal y) (A.tensor B) := by
    refine ⟨hsemi.1.mul hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hev : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Λ sg) := by
      filter_upwards [hBloc z hz sg hsg, eventually_blocks_ne_zero hz.1] with x h1 h2
      rw [show (A.tensor B).h x = A.h x * B.h x from rfl, h1,
        Real.log_mul (A.pos x h2).ne' (hΛ sg).ne']
    rw [leviForm_congr_add_const _ hev]
    exact hsemi.2 z hz w hw
  have hconj' : IsConjInvariantH (A.tensor B) := fun z => by
    show A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  have hmon' : MonomialsBounded (mCoordIdeal y) (A.tensor B) a := by
    intro z hz μ hμ
    obtain ⟨sg, hsg, -⟩ := huniq z hz
    have hb := hmon z hz sg hsg μ hμ
    have hBz : B.h z = Λ sg := (hBloc z hz sg hsg).eq_of_nhds
    show _ ≤ A.h z * B.h z
    rw [hBz, mul_comm]
    exact hb
  have h0 := hG1 K ι Ω y D a (A.tensor B) P0 II hD hII hvar hbir hA' hP0 hsemi' hmon' hconj'
  rwa [hT K ι Ω F y D a A B II Λ hD hII hvar hbir ha hsemi.1 hBa hBs hΛ huniq hBloc] at h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem LiftPrime.proof (h : Lift.Statement) : LiftPrime.Statement := h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem MetricToFS.proof (hE : PullFSExtension.Statement) (hC : DefectMetricChange.Statement) :
    MetricToFS.Statement := by
  intro D Ω _ _ κ _ I d e hI hF
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hE D Ω κ d.x e hF
  exact ⟨d.withMetric m₀ ⊥ hs hc bot_le hp, rfl, hpull,
    hC D Ω κ I d m₀ ⊥ hs hc bot_le hp e hI hF⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace SlopeLowerBound

theorem succ_rpow_isLittleO (D : ℕ) (hD : 1 ≤ D) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have hcast : (D : ℝ) - 1 = ((D - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hD, Nat.cast_one]
  have h1 : (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) = fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1) := by
    funext n; rw [hcast, Real.rpow_natCast]
  rw [h1]
  have hO : (fun n : ℕ => ((n : ℝ) + 1) ^ (D - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (D - 1) := by
    refine IsBigO.of_bound (2 ^ (D - 1)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  exact hO.trans_isLittleO ((isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show D - 1 < D by omega)).comp_tendsto
    tendsto_natCast_atTop_atTop)

theorem proof (hHSM : TheoremHSM.Statement) (hRank : RankOfSections.Statement)
    (hGen : GenericFibre.Statement) (hRk : SectionsRank.Statement) (hPos : DegreePositive.Statement) :
    SlopeLowerBound.Statement := by
  intro D Ω _ _ κ _ I d hI ε hε
  obtain ⟨hqP, hqd⟩ := hGen Ω κ d.x D d.arith
  obtain ⟨C, hC⟩ := hRank κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hδ0 := hPos ℚ κ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) D hqP hqd
  have hg : genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) := by
    unfold genDeg
    convert rfl
    simp
  have hδ : (0 : ℝ) < (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) := by rw [hg]; exact_mod_cast hδ0
  have hrank : ∀ n : ℕ, |(Module.finrank ℤ (sec ℤ d.x n) : ℝ) -
      (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1) := by
    intro n
    have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ d.x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) =
        (Module.finrank ℤ (sec ℤ d.x n) : ℝ) := by exact_mod_cast hRk Ω κ d.x n
    rw [← e, hg]
    exact hC n
  set δ : ℝ := (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) with hδdef
  set T : ℝ := top I d.x d.m D with hTdef
  set r : ℕ → ℝ := fun n => (Module.finrank ℤ (sec ℤ d.x n) : ℝ) with hrdef
  have hfD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hfac : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  set c : ℝ := T / (((D : ℝ) + 1) * δ) with hcdef

  have hR : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / D.factorial) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.trans_isLittleO ?_ (succ_rpow_isLittleO D d.one_le)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hrank n

  have hH : (fun n : ℕ => resChi d n - T * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop] pw D :=
    (hHSM D Ω κ I d hI).1

  have hE : (fun n : ℕ => resChi d n - c * n * r n) =o[atTop] pw D := by
    have h2 : (fun n : ℕ => (c * (n : ℝ)) * (r n - δ * (n : ℝ) ^ D / D.factorial)) =o[atTop] pw D := by
      refine (((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left c).mul_isLittleO hR).congr
        (fun _ => rfl) ?_
      intro n; simp only [pw]; ring
    refine (hH.sub h2).congr (fun n => ?_) (fun _ => rfl)
    rw [hcdef, hfac]
    field_simp
    ring

  have hlow : ∀ᶠ n : ℕ in atTop, δ / (2 * D.factorial) * (n : ℝ) ^ D ≤ r n := by
    filter_upwards [hR.def (show 0 < δ / (2 * D.factorial) by positivity)] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)] at hn
    have h1 := neg_abs_le (r n - δ * (n : ℝ) ^ D / D.factorial)
    have e : δ * (n : ℝ) ^ D / D.factorial = 2 * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
      field_simp
    linarith
  filter_upwards [hlow, hE.def (show 0 < ε * (δ / (2 * D.factorial)) by positivity), eventually_ge_atTop 1]
    with n hn hEn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hrpos : 0 < r n := lt_of_lt_of_le (by positivity) hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ pw D n)] at hEn
  have hslope : T * n / (((D : ℝ) + 1) * δ) = c * n := by rw [hcdef]; ring
  show T * n / (((D : ℝ) + 1) * δ) - ε * n ≤ resChi d n / r n
  rw [hslope, le_div_iff₀ hrpos]
  have h1 : ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) ≤ ε * n * r n :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have h2 := neg_abs_le (resChi d n - c * n * r n)
  have h4 : ε * (δ / (2 * D.factorial)) * pw D n = ε * n * (δ / (2 * D.factorial) * (n : ℝ) ^ D) := by
    simp only [pw]; ring
  linarith

end SlopeLowerBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resolutionVolumeL2_le_sqrt_two_mul (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) :
    resolutionVolumeL2 d n f ≤ Real.sqrt 2 * resolutionSectionL2Norm d n f := by
  unfold resolutionVolumeL2 resolutionSectionL2Norm
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have hb : 0 ≤ ∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (conjPt (resPt d y)) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  linarith

theorem TheoremHSM.proof (h₁ : ReductionToProjective.Statement) (h₂ : HilbertSamuelProjective.Statement)
    (h₃ : ResolutionSupBound.Statement) : TheoremHSM.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨?_, ?_⟩
  · have hA := (h₁ D Ω κ I d hI).2
    have hB := (h₂ D I hI).const_mul_left (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ)
    exact (hA.add hB).congr_left fun n => by ring
  · obtain ⟨C, hC⟩ := ResolutionSupBound.toInt h₃ D Ω κ d
    refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
    have hp : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
    have hv : 0 ≤ resolutionVolumeL2 d n f := Real.sqrt_nonneg _
    calc ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          hC n hn f hf z hz
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) hv
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * resolutionSectionL2Norm d n f) :=
          mul_le_mul_of_nonneg_left (resolutionVolumeL2_le_sqrt_two_mul d n f)
            (mul_nonneg (le_max_right _ _) hp)
      _ = max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionSectionL2Norm d n f := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TopPullFS

variable {κ : Type} [Fintype κ] {D : ℕ}

theorem linApply_projMat (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) (k : Fin (D + 1)) :
    linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z ⟨(), k⟩ = z (e k) := by
  classical
  simp only [linApply, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem fs_linApply (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))).h
        (linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z) =
      Real.sqrt (∑ k, ‖z (e k)‖ ^ 2) := by
  simp only [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linApply_projMat]

end TopPullFS

open TopPullFS in

theorem TopPullFS.proof (hCM : ChangeOfModelStatement) (hBP : ProjFrameBasePtFree.Statement)
    (hIm : ProjFrameImage.Statement) (hDeg : ProjFrameGraphDeg.Statement) : TopPullFS.Statement := by
  intro D Ω _ _ κ _ I x m e hI hP hm hfr hFS
  obtain ⟨G, J, hJ, hJe⟩ := hDeg D Ω κ x e hP hfr
  have himg := hIm D Ω κ x e hfr
  have key := hCM I hI Unit (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x) (D + 1) (projMat e) G J
    (fun _ => HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))) (fun _ => HermLine.ofCone m) hP
    (hBP D Ω κ x e hfr) (by rw [himg]; exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot D) hJ
    (fun _ => IndefiniteRowSideFullHecke.HilbertSamuel.P1.isSmoothHerm_fs) (fun _ => isSmoothHerm_ofCone hm) (fun _ => rfl)
    (fun _ z hz => by
      rw [fs_linApply]
      exact hFS z ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩)
  rw [himg, hJe] at key
  simpa [top, hhOf] using key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem TheoremHSM.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full) ResolutionSupBound.full)

theorem TheoremHSMBlock.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionImageSup.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegreeIntegral.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement)
    (h13 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h14 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.Statement)
    (h15 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h16 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphDeg.Statement)
    (h17 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h18 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjectiveBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMetricChange.proof BlockMeasureChange.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockDefectMetricChange.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockRealGramComparison.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionSupBound.proof h10 NonvanishingDense.full) SupBoundBlock.full
  SupBoundCount.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockComplexGramMetricChange.proof MetricChange.full
  BlockResolutionMetricPair.full BlockResolutionFormsIndependent.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegree.proof BlockSectionsRank.full h11))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof h12 BlockResolutionInterpIntegral.full)
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h13 Closed.PtsSumMeasurable)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageDatum.proof BlockImageArith.full h14 AnResNullForm.full
  BlockImageMetrics.full BlockImageChi.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageTop.proof h15
  BlockGraphImage.full h16) BlockImageGenDeg.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h17)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h15 VeroneseArith.full VeroneseGraphImage.full h18)
  VeroneseGenDeg.full) PointHeightFS.full) SupBoundBlock.full)

theorem HilbertSamuelProjective.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full)

theorem ReductionToProjective.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))

theorem SlopeLowerBound.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.SlopeLowerBound.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SlopeLowerBound.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full) ResolutionSupBound.full) RankOfSections.full GenericFibre.full
  SectionsRank.full DegreePositive.full)

theorem SuccessiveMinimaDual.of_open
    (h0 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.IrreducibleConnected.Statement)
    (h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (h3 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement)
    (h4 : GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResInt.Statement)
    (h5 : GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsAdditive.Statement)
    (h6 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IntBridge.Statement)
    (h7 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResComps.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaDual.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaDual.proof G1.full EmbeddingWeight.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h0 Closed.PtsSumMeasurable))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.PieceIntegral.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ClopenDegree.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.ClopenComponents.proof
  h1) (GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentDegree.proof (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3
  Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint) h3 h4) h5 IntNumComponents.full)) ConjIntNum.full))
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h6 h7 (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3 Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint)))))

theorem G2.of_open
    (h0 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IntBridge.Statement)
    (h1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResComps.Statement)
    (h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (h3 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement)
    (h4 : GroundTheory.Heights₂.Heights.HilbertSamuel.FujitaGeneric.Statement)
    (h5 : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartLatQCech.Statement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.EulerHilbert.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionLatticeFinite.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.DiagonalSectionDifference.Statement)
    (h9 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.G2.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.G2.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaSection.proof
  NefOnGenericOfSemipos.full (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h0 h1
  (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3
  Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint))) (GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefSectionGrowth.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefShiftPolynomial.proof h4 h5 h6 EventualPolyLine.full)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftSectionBound.proof h7
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftQuotientBound.proof h7
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneQuotientBound.proof HyperplaneRegularSection.full h8 h7)
  HyperplaneRegularSection.full))) (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneSectionBound.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneQuotientBound.proof HyperplaneRegularSection.full h8 h7)))
  ChartDenominator.full SectionSupBound.full) SectionProduct.full PerturbSemipos.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.proof h9
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h0 h1 (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3 Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint)))) h10 ZCombLimit.full)

theorem Lift.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    (h2 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.proof h0 h1 (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof
  LiftSpread.full (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof GeneratedPow.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof h2 QuotPartGraded.full h3 h4 ReductionComplex.full
  ZeroCocycleSection.full SecCochReduce.full) FibreRelLift.full) LiftBirationalAmple.full))

theorem LiftPrime.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    (h2 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftPrime.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftPrime.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.proof h0 h1
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof LiftSpread.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof GeneratedPow.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof h2 QuotPartGraded.full h3 h4 ReductionComplex.full
  ZeroCocycleSection.full SecCochReduce.full) FibreRelLift.full) LiftBirationalAmple.full)))

theorem Perturb.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechComplex.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechExact.Statement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.Perturb.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.Perturb.proof SmallGenTwist.full SemiposTwist.full GenDegTwist.full
  GenOnFibres.full (GroundTheory.Heights₂.Heights.HilbertSamuel.AmpleOfGenTwist.proof GenTwistGenerated.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistVanish.proof h0 QuotPartGraded.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.GenKoszulStep.proof h1 h2 DoubleComplexVanish.full h3 h4))))

theorem IntegralClosureFinite.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.SecEqStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralClosureFinite.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralClosureFinite.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRational.proof h0) NmSectionsFinite.full)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
