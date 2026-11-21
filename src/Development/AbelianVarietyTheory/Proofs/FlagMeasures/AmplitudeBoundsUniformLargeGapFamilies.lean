import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpBoundsUniformOfInputs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdDiffEqProdFactorial
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGapStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_besselFunction_largeGaps : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → D.host.rdE ≤ large₂.sc.b → m₀ ≤ D.R.m → cdScaleTie D → Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca := by
  first | exact @GlobalTheory.AmpBesselGap.ampIsBessel | exact GlobalTheory.AmpBesselGap.ampIsBessel | (intros; apply GlobalTheory.AmpBesselGap.ampIsBessel <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneBessel_torusTranslates_largeGap : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  first | exact @GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | exact GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | (intros; apply GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp <;> assumption)
end

section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPointwiseBound_at_largeGaps : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  first | exact @GlobalTheory.bp_forms_of_gapIn_thmBpDS | exact GlobalTheory.bp_forms_of_gapIn_thmBpDS | (intros; apply GlobalTheory.bp_forms_of_gapIn_thmBpDS <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (GlobalTheory.T.besselPointwiseBound_at_largeGaps hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.T.oneBessel_torusTranslates_largeGap hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.T.amplitude_eq_besselFunction_largeGaps hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  atlas_forward_decl GlobalTheory.UnifPTGap.uniformPT_gap
end

section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLength_moments_amplitudes_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  first | exact @GlobalTheory.AmpMomentsGap.amplitude_moments_gap | exact GlobalTheory.AmpMomentsGap.amplitude_moments_gap | (intros; apply GlobalTheory.AmpMomentsGap.amplitude_moments_gap <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section
open GlobalTheory.Amp

namespace GlobalTheory.GapUAmp

theorem abs_all_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn C) ∧ (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) := by
  intro _ hH _ Cg cb Cu cT CT C0 A C1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.T.majorantLength_moments_amplitudes_largeGap hH Cg cb Cu cT CT C0 C1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRange.abs_range Cg cb Cu cT CT C0 C1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, 1000, le_max_right _ _, ?_⟩
  intro eps Fm _ hCl _
  have key : ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
      ABSr (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 (max C₀ 0) := by
    intro Cn
    obtain ⟨m₂, hM⟩ := hMo Cn
    obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₁ m₂) 1)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨-, hm, -, -, hrd, -⟩ := hx0 x hx i
    have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hm
    have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1 → Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
      fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
    exact hAbs' Cn _ _ _ _ (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
      (hM _ _ _ _ hCl (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
  refine ⟨fun Cn => (key Cn).mono ?_, (key 0).mono ?_⟩
  · intro C' Cl x i h τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2
  · intro C' Cl x i h τ w w' hTT θ hθ W hW S hS _ γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW (lamD _ τ) (by simp [l1dist]) S hS γ p hp θ' hθ' νR hR hD).1

end GlobalTheory.GapUAmp
end
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapDegreeRatio

theorem deg_eq_of_goodS (hH : GlobalTheory.GapIn.Hyp) (D : D7) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : LocW D.R.k D.R.rS) (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ),
      GoodS D l A → GapAtLeast (epsSH D.R) l h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h →
      A.deg = c * Formalism.QuantumDeterminants.fdegHC l := by
  obtain ⟨c, hc, hF⟩ := hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)
  set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs
  have hs0 : 0 < s := D.s.cdScale_pos _ _
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  refine ⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩
  obtain ⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩ := hA
  have hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l) :=
    hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS
  have hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q))
      (c * Formalism.QuantumDeterminants.fdegHC l / s) := by
    refine ⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]
    have hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hFQ.1.ne'
    have hcc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'.ne'
    push_cast at hd0 ⊢
    field_simp
  have : Nontrivial A.H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩
  have h1 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw
  rw [← h1, h2]
  ring

theorem deg_ratio : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  intro hH D W l l' A A' h hA hA' hg hg' hok
  obtain ⟨c, hc, hk⟩ := deg_eq_of_goodS hH D
  rw [hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]
  exact mul_div_mul_left _ _ hc.ne'

end GlobalTheory.GapDegreeRatio
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  atlas_forward_decl GlobalTheory.GapDegreeRatio.deg_ratio
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gap_near_placeParameter_half_noncompactGap : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  atlas_forward_decl GlobalTheory.GapNear.gap_near
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.DegStepG

theorem vandLine (hH : GlobalTheory.GapIn.Hyp) (Cn m₀ : ℝ)
    (hnear : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
      1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
        l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r →
        Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2))
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ) (hCl : 1000 ≤ Cl) (hm : m₀ ≤ D.R.m) :
    Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro hH0 τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hZ : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := hH0
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  obtain ⟨g1, gok⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ lam' h1
  obtain ⟨g2, _⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ _ h2
  exact GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap hH D W lam' (lam' + s • epsI I) A A' _ hA hA' g1 g2 gok

theorem degI_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ,
        OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  refine ⟨1, 1000, zero_le_one, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hnear⟩ := GlobalTheory.T.gap_near_placeParameter_half_noncompactGap Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i => ?_⟩
  exact Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
    (vandLine hH Cn m₀ hnear (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ _ _ hCl (hx0 x hx i).2.1)

end GlobalTheory.DegStepG
end
end

section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ → ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W, (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) → ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ, (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧ (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧ ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ := by
  first | exact @GlobalTheory.CellMinorLineGap.minor_line | exact GlobalTheory.CellMinorLineGap.minor_line | (intros; apply GlobalTheory.CellMinorLineGap.minor_line <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_ratio_statement : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := by
  first | exact @GlobalTheory.MassAtRecord.massRatio_at_record | exact GlobalTheory.MassAtRecord.massRatio_at_record | (intros; apply GlobalTheory.MassAtRecord.massRatio_at_record <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem along_family_of_massRatio (hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hE hF eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low _ _ _ _ _ _ _ _ _ _ hCl (vv_eq hE hF _ (Fm.ties x i)) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

theorem along_family :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :=
  along_family_of_massRatio GlobalTheory.T.mass_ratio_statement

end GlobalTheory.CritLevel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.AmpFamGap

theorem cellConv : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence

theorem amplitudeNormDegree_along_family_of_kFiniteIdentity : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro hH hA Cg cb Cu cT CT C0 C1
  refine ⟨1000, fun eps Fm hC' hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap hH hA cellConv Cg cb Cu cT CT C0 C1 Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i hZ => ?_⟩
  obtain ⟨-, hm0, -, -, hrd, -⟩ := hx0 x hx i
  have hm2 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have := (Fm.D x i).R.two_le_m
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.m)
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hm0⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hZ

theorem amplitudeNormDegree_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro _ hH _
  exact amplitudeNormDegree_along_family_of_kFiniteIdentity hH (GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap hH)

end GlobalTheory.AmpFamGap
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmpUniform

theorem weyl_fam_gap : ∀ (eps : ℝ) (Fm : FamP eps), VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm := by
  intro eps Fm x i τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (GlobalTheory.CritLevel.isHCParam_uS (Fm.D x i) w τ)).1 H _ hg

theorem amplitude_bounds_uniform_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CPT, t1, hPT⟩ := GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨CDl, t2, hDl⟩ := GlobalTheory.FamDlGap.ptDl_along_family_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨t3, h5⟩ := GlobalTheory.CritLevelGap.tcritLow_along_family_gap hM hH hB Cg cb Cu cT CT C0
  obtain ⟨t4, h9⟩ := GlobalTheory.AmpFamGap.amplitudeNormDegree_along_family_largeGaps hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨hilbertNinetyConstant, t5, hilbertNinetyConstant_pos, hDeg⟩ := GlobalTheory.DegStepG.degI_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨Ca, t6, hCa, hAC⟩ := GlobalTheory.GapUAmp.abs_all_along_family_gap hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CS, t8, hS⟩ := GlobalTheory.GapAmp.schur_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.ampBounds_uniform_of_inputs Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  refine ⟨C, C2, Ch, max t1 (max t2 (max t3 (max t4 (max t5 (max t6 t8))))), hC, hCh, ?_⟩
  intro eps Fm h1 h2 hR Cpr δ hδ
  exact H eps Fm
    (hPT eps Fm ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) hR)
    (hDl eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h5 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h9 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hDeg eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).1
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).2
    (hS eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (weyl_fam_gap eps Fm) Cpr δ hδ

end GlobalTheory.GapAmpUniform
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_bounds_uniform_large_gap_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  atlas_forward_decl GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap
end
