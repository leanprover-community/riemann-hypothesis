import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpUnifPOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypothesesStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMultOneDecayOfLargeGapHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily

section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataNW_of_standingNumericalData : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  first | exact @GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | exact GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | (intros; apply GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem ampAt_record_of_inputs :
    ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam →
      VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT →
      VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl →
      VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 →
      VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 →
      DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant →
      AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca →
      VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D →
      AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  intro Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0
  set Cc : ℝ := CS + Cg + 2 with hCc
  set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK
  set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd
  set Cm : ℝ := max (max K Ca) 2 with hCm
  set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd
  set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2
  have m1 : K ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : Ca ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : 2 ≤ Cm := le_max_right _ _
  have n1 : Cm ≤ C := le_max_left _ _
  have n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hChA : max (CDl + 1) 0 ≤ Ch := le_max_right _ _
  have hCh0 : 0 ≤ Ch := le_trans (le_max_right _ _) hChA
  have hChD : CDl ≤ Ch := le_trans (le_max_left _ _) (le_max_left _ _)
  have h62 : 6 * C ≤ C2 := le_max_left _ _
  have h22 : C ^ 2 + C * Ch ≤ C2 := le_max_right _ _
  refine ⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩
  obtain ⟨thr0, hthr0⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))
  refine ⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩
  by_cases hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0
  swap
  · refine ⟨?_, ?_, ?_⟩
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
      exact absurd hH.1 hH0
  obtain ⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩ := hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm
  have hMC : C ≤ (D.R.k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk
  have hMd : 1 / δ ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm
  have hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb : 1 ≤ large₂.sc.b := one_le_b large₂

  have hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch := by
    refine heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_
    nlinarith
  have hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch :=
    product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22

  have hCl1 : 1 / Cl ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc :=
    constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12

  have hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := by
    calc (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hrb (mul_nonneg hilbertNinetyConstant_pos hm0)
      _ ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith)
  have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two D
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k := by
    have hmpos : (0 : ℝ) < D.R.m := by rw [hmr]; positivity
    have e1 : 1 ≤ δ * (D.R.m : ℝ) := by
      rw [div_le_iff₀ hδ] at hMd; linarith
    have e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right e1 hmpos.le
      nlinarith
    have e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k := mul_le_mul_of_nonneg_left hm2k hδ.le
    linarith

  have r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _)
      m1 hCh0 hChD hA1 hA2 p1
  have r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    abs_decay_mono_constants D large₂ hCa0 m2 hChA
      (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _)
        (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) hn hA2 hA9 hDeg hAbs)
  have q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ :=
    decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2
  exact ⟨hS3, hS5, q7⟩

end GlobalTheory

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampAt_of_admitted_bounds : ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl → VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 → DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant → AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  atlas_forward_decl GlobalTheory.ampAt_record_of_inputs
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem ptWide_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hDB : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  have hBp : BpJoin.ThmBpDS := GlobalTheory.discreteSeriesCoef_pointwiseBound
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hDB
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Cb, Cg₀, hB⟩ := GlobalTheory.bp_forms_of_gapIn_thmBpDS hDB hBp 1
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.AmpBesselGap.ampIsBessel hDB Cg cb Cu cT CT C0 1
  refine ⟨max (Ca + max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0),
    fun Cn => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hAmp Cn
  obtain ⟨Cs₀, hCs₀⟩ := hFrm Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ (max (128 * |max Cg₀ Cs₀|) (200 * |Cn|)))
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hTies hTF => ?_⟩
  intro hH
  obtain ⟨h1000, -, hM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH.1
  have hβ2 : (2 : ℝ) ≤ max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hStd : Bridge.StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|)
      (max (max 2 Cu) (max CT (1 / 8 + 2 * Cg))) :=
    stdOfHyp_rec D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|) _ (by linarith) zero_le_one hβ2
      (le_trans (le_max_right _ _) (le_max_left _ _))
      (by rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by rw [mul_one]; exact le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
      (by
        rw [abs_of_nonneg (by positivity)]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  have h47 : OnePlaceEstimates.UniformityTheoremBPrime D 1 Cn (max Cg₀ Cs₀) (200 * |Cn|) (max Cb 0) :=
    OnePlaceEstimates.upper_bound_mono_constant D zero_lt_one (le_max_left _ _)
      ((hB (max Cg₀ Cs₀) (le_max_left _ _)).2.2 D Cn (200 * |Cn|)
        (mul_le_mul_of_nonneg_left (le_abs_self Cn) (by norm_num)))
  have hFr : Bridge.FrameChange D 1 (max Cg₀ Cs₀) Cn Cf :=
    hCs₀ (max Cg₀ Cs₀) (le_max_right _ _) D (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D))
  exact AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 Ca 1 Cf (max Cg₀ Cs₀) (200 * |Cn|) _ (max Cb 0) _
    (hm₀ D large₂ C' Cl h1000 hrd (le_trans (le_max_left _ _) hM) hTies.cdScale_tie) hFr hStd (fun _ => hTF) h47
    (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _) hH

end GlobalTheory.Core.Deg
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleTheta_wideRange_large_constants : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  atlas_forward_decl GlobalTheory.Core.Deg.ptWide_at_record_gap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreDlGap

theorem ptDl_at_record : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C, hC⟩ :=
    GlobalTheory.CellMinorLineGap.minor_line hH (GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1
  refine ⟨C, fun Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hH0
  obtain ⟨hCl, -, hMm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hMm
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hMm
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl hCl hbig hT.cdScale_tie hH0

end GlobalTheory.CoreDlGap
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AmpRec

theorem exists_threshold_adm9_of_ties : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  intro Cg cb Cu cT CT C0 Cn
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨m₀, hm⟩ := GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH (GlobalTheory.AmpOrbGap.ampKF hH)
    GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1 Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hT => ?_⟩
  intro hH0
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hmM
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hmM
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl h1000 hbig hT.cdScale_tie hH0

end GlobalTheory.AmpRec
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  atlas_forward_decl GlobalTheory.AmpRec.exists_threshold_adm9_of_ties
end

section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.AbsRange
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRangeUniform

theorem abs_range_constants_first : ∀ Cg cb Cu cT CT C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl C0 hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dif_pos (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dif_pos l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRangeUniform
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AbsRecGap

theorem abs_all_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Formalism.MainNotions.BridgeLemma.AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cn C := by
  intro Cg cb Cu cT CT C0
  have hG : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.AmpMomentsGap.amplitude_moments_gap hG Cg cb Cu cT CT C0 1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRangeUniform.abs_range_constants_first Cg cb Cu cT CT 1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, le_max_right _ _, fun Cn => ?_⟩
  obtain ⟨m₂, hM⟩ := hMo Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max (max m₁ m₂) 1000)
  refine ⟨thr, ?_⟩
  intro D large₂ C' Cl hC' hCl τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
  have h0 : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := by
    unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
  obtain ⟨h1000, -, hm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl h0.1
  have hm1000 : (1000 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hm
  have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1000 → GlobalTheory.Amp.Big D large₂ Cl m₀ :=
    fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
  exact (hAbs' Cn D large₂ C' Cl C0 (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
    (hM D large₂ C' Cl h1000 (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
    h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2

end GlobalTheory.AbsRecGap
end

section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeSchurBound_uniform_constants : ∀ Cg cb Cu cT CT C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  first | exact @GlobalTheory.Amp.schurSt_of_big_tie_uniform | exact GlobalTheory.Amp.schurSt_of_big_tie_uniform | (intros; apply GlobalTheory.Amp.schurSt_of_big_tie_uniform <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Amp

theorem schur_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C₀, hC⟩ := GlobalTheory.T.amplitudeSchurBound_uniform_constants Cg cb Cu cT CT 1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses hH Cg cb Cu cT CT C0
  obtain ⟨thr, hthr⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max m₀ m₁) 1)
  refine ⟨C₀, thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hZ
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hZ.1
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ Cl * (D.R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → Big D large₂ Cl m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm D large₂ C' Cl C0 (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) hT.cdScale_tie
    (GlobalTheory.GapAmp.bessel_schur_gap hH D large₂ C' Cl Cg cb Cu cT CT C0 h1000)
    (hL D large₂ C' Cl (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _)))) hZ

end GlobalTheory.Amp
end

section
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpRecordGap

theorem isHCParam_u (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨c, hc⟩ := R.k_even
  have step : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := fun i h =>
    lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
  refine ⟨?_, fun a => ?_⟩
  · have key : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : P.u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = P.u j := congrArg P.u (Fin.ext (by simp; omega))
    rw [e] at this
    beta_reduce
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - c + 1, ?_⟩
    simp only
    rw [hz, hc]; push_cast; ring

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) :=
  isHCParam_u D.R (D.hcW w τ)

theorem weyl_at (D : D7) : VanishingOnXAndXPlusBranching.adm12 D := by
  intro τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D w τ)).1 H _ hg

theorem ampOn_singleton : ∀ c : ℝ, AmpOn {c} := by
  intro c Cg cb Cu cT CT hcb _
  obtain ⟨CPT, hPT⟩ := GlobalTheory.T.ampleTheta_wideRange_large_constants Cg cb Cu cT CT c
  obtain ⟨CDl, hDl⟩ := GlobalTheory.CoreDlGap.ptDl_at_record Cg cb Cu cT CT c
  obtain ⟨Ca, hCa, hAbs⟩ := GlobalTheory.AbsRecGap.abs_all_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CS, tS, hS⟩ := GlobalTheory.Amp.schur_at_record_gap Cg cb Cu cT CT c
  obtain ⟨tL, hL⟩ := GlobalTheory.T.exists_threshold_criticalLevel_lower_bound cb Cu hcb
  obtain ⟨tV, hV⟩ := GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.T.ampAt_of_admitted_bounds Cg CPT CDl 1 Ca CS zero_le_one hCa
  refine ⟨C, C2, Ch, hC, hCh, fun Cpr δ hδ => ?_⟩
  obtain ⟨t0, H0⟩ := H Cpr δ hδ
  obtain ⟨t1, h1⟩ := hPT (max Cpr 0)
  obtain ⟨t2, h2⟩ := hDl (max Cpr 0)
  obtain ⟨t3, h3⟩ := GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree Cg cb Cu cT CT c (max Cpr 0)
  obtain ⟨t4, h4⟩ := hAbs (max Cpr 0)
  obtain ⟨t5, h5⟩ := GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line (max Cpr 0)
  refine ⟨max t0 (max t1 (max t2 (max t3 (max t4 (max tS (max tL (max tV t5))))))),
    fun C0 hC0 C' Cl hC' hCl D large₂ hG hT _ hTF => ?_⟩
  obtain rfl : C0 = c := hC0
  simp only [max_le_iff] at hC' hCl
  obtain ⟨a0, a1, a2, a3, a4, aS, -, aV, a5⟩ := hC'
  obtain ⟨b0, b1, b2, b3, b4, bS, bL, bV, b5⟩ := hCl
  have hLow : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 := fun h0 =>
    hL D large₂ C' Cl Cg cT CT C0 bL
      (hV D large₂ C' Cl Cg cb Cu cT CT aV bV hT h0.1 (GlobalTheory.T.dataNW_of_standingNumericalData D C0 h0.2.2 h0.2.1)) h0
  exact H0 D large₂ C' Cl cb Cu cT CT C0 a0 b0 hG
    (h1 D large₂ C' Cl a1 b1 hT hTF)
    (h2 D large₂ C' Cl a2 b2 hT)
    hLow
    (h3 D large₂ C' Cl a3 b3 hT)
    (Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
      (h5 D large₂ C' Cl Cg cb Cu cT CT C0 1 a5 b5 hT))
    (h4 D large₂ C' Cl a4 b4)
    (hS D large₂ C' Cl aS bS hT)
    (weyl_at D)

end GlobalTheory.AmpRecordGap
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width : ∀ c : ℝ, AmpOn {c} := by
  atlas_forward_decl GlobalTheory.AmpRecordGap.ampOn_singleton
end
