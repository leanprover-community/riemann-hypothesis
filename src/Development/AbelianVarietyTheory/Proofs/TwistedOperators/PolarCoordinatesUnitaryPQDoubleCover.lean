module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitPStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobianStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLogStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnPStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvdStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementPStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompactStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitPStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigenStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementPStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

theorem polJ_aOf_eq_prod (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  apply GlobalTheory.CartanInt.polJ_aOf <;> assumption

theorem shc_pos (x : ℝ) : 0 < shc x := by
  unfold shc
  split_ifs with hx
  · exact one_pos
  · rcases lt_or_gt_of_ne hx with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

theorem polJ_conj {p q : ℕ} (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) (Y : Mat p q) :
    polJ (matG T k * Y * matG T k⁻¹) = polJ Y :=
  GlobalTheory.T.polarJacobian_blockDiag_conj_invariant p q _ _ Y (by rw [← matG_mul, mul_inv_cancel, matG_one]) hk ((Ksub T).inv_mem hk)

theorem exists_conj_aOf {p q : ℕ} (T : GrpData p q) {Y : Mat p q} (hY : Y ∈ pR p q) :
    ∃ k ∈ T.Kset, ∃ h : ℕ → ℝ, Y = matG T k * aOf p q h * matG T k⁻¹ := by
  obtain ⟨B, rfl⟩ := exists_pY hY
  obtain ⟨U, hU, V, hV, h, hB⟩ := GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose p q (Matrix.of B)
  obtain ⟨k, hk, hkm⟩ := GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal p q T U hU V hV
  refine ⟨k, hk, h, ?_⟩
  rw [matG_inv_of_mem T hk, hkm, pY, hB]
  simp [aOf, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

theorem polJ_pos {p q : ℕ} (T : GrpData p q) (B : Fin p → Fin q → ℂ) : 0 < polJ (pY B) := by
  obtain ⟨k, hk, h, hB⟩ := exists_conj_aOf T (pY_mem B)
  rw [hB, polJ_conj T hk, polJ_aOf_eq_prod]
  exact Finset.prod_pos fun _ _ => shc_pos _

theorem cartan {p q : ℕ} (T : GrpData p q) (g : T.G) : ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  by_cases h : 1 ≤ p + q
  · exact (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q h T).2 g
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    refine ⟨g * (T.expt (pY 0))⁻¹, ?_, pY 0, pY_mem 0, by simp⟩
    intro a
    rcases a with a | a <;> exact a.elim0

theorem isAddHaar_volume (p q : ℕ) : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem haar_polar {p q : ℕ} (T : GrpData p q) :
    ∃ (c : ℝ) (mK : Measure T.G), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (T.Kset)ᶜ = 0 ∧
    (∀ k ∈ T.Kset, Measure.map (fun x => k * x) mK = mK) ∧
    ∀ f : T.G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂T.haar = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ,
          (∫⁻ k, f (k * T.expt (pY B)) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  obtain ⟨-, hinv, hlc, hsc, ht2⟩ := GlobalTheory.T.unitaryPQCover_unimodular p q T
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ := GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' T.G (Ksub T) (GlobalTheory.T.isCompact_detSqrtCover_maxCompact p q T)
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.T.exists_continuousOn_polar_log' p q
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (GlobalTheory.T.continuous_polarCoordinatesJacobian p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ p q _ (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q B)
  have hem : Measurable fun B : Fin p → Fin q → ℂ => T.expt (pY B) := (continuous_expt_pY T).measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal T.G (Fin p → Fin q → ℂ) T.haar mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) T.Kset (fun B => T.expt (pY B)) hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI := isAddHaar_volume p q
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ)) Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using polJ_pos T B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (matG T '' C)) :=
        (hC.image (continuous_matG T)).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact Units.isUnit _))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [matG_mul, matG_expt]
      exact hL _ B (matG_star_mul T hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p p q T L hLc hL (cartan T) g
      refine ⟨ψ, hψc.measurable, GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords p q (matG T g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := exists_blocks T hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg (matG T) h
          rwa [matG_mul, matG_mul, matG_expt, matG_expt, hm] at this)
        (fun B => by rw [hdet]; exact polJ_pos T B) (GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP p q)
        (fun B => GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP p q B (GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × T.G => f (z.2 * T.expt (pY z.1)))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

theorem polar_coordinates : ∀ X : ProvA, CoverHaarIntegration X := by
  intro X p q
  refine ⟨haar_polar (X.grp p q), fun k hk Y _ => ?_, fun Y hY => ?_, fun h => ?_⟩
  · rw [← matG_inv]; exact polJ_conj _ hk Y
  · obtain ⟨k, hk, h, hY⟩ := exists_conj_aOf (X.grp p q) hY
    exact ⟨k, hk, h, by rw [← matG_inv]; exact hY⟩
  · rw [polJ_aOf_eq_prod, GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP]

end GlobalTheory.PolarU
