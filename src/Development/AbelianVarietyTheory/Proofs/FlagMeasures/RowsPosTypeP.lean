import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBesselStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesSecond
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGap
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesFirst
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm

theorem locDatC_of_besselOfW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) : LocDatC := by
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  intro D X hne hG hT
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  refine ⟨C, hB, Formalism.L2.SG.Pf.LocF.locFactor_holds hG C, fun u τ => ⟨?_, ?_⟩⟩
  · exact goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  · exact goodS_of _ u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT _ u u τ)

end GlobalTheory.TypeAsm
end
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.TailTwo

theorem cheb_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T ≤ l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx) n

theorem meas_closed (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsClosed t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := (continuousOn_iff_isClosed.1 hg) t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsClosed.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem meas_open (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsOpen t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 hg t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

end GlobalTheory.Amp.TailTwo

namespace GlobalTheory.Amp.TailTwo

theorem tailBd_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  intro k r Wp _ _ _ z νS Φ q H₁ _ hH hG _ hM hI la hla
  set T : ℝ := la * H₁ with hTdef
  have hT : 0 < T := mul_pos hla hH
  set f : Mt k r → ℝ≥0∞ := fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 with hf
  set A : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ici T} with hA
  set B : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ioi 0} ∩
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Iic T⁻¹} with hB
  set N : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hN
  have hGc : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have hNm : MeasurableSet N := hGc.compl
  have hAm : ∀ a, MeasurableSet (A a) := fun a =>
    meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Ici
  have hBm : ∀ a, MeasurableSet (B a) := fun a =>
    (meas_open k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isOpen_Ioi).inter
      (meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Iic)
  set U : Set (Mt k r) := N ∪ ⋃ a, (A a ∪ B a) with hU
  have hUm : MeasurableSet U := hNm.union (MeasurableSet.iUnion fun a => (hAm a).union (hBm a))
  have hsub : {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹} ⊆ U := by
    rintro x ⟨a, ha⟩
    by_cases hx : Matrix.of x ∈ GG k r
    · refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
      rcases le_max_iff.1 ha with h | h
      · exact Or.inl ⟨hx, h⟩
      · have hpos : 0 < lA k r z (Matrix.of x) a := inv_pos.1 (lt_of_lt_of_le hT h)
        refine Or.inr ⟨⟨hx, hpos⟩, hx, ?_⟩
        show lA k r z (Matrix.of x) a ≤ T⁻¹
        exact (le_inv_comm₀ hT hpos).1 h
    · exact Or.inl hx
  have hc : ∀ a, ∫⁻ x in A a ∪ B a, f x ∂νS ≤ 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
    intro a
    have key : ENNReal.ofReal ((T ^ (2 * q))⁻¹) * (ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) =
        ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.rpow_neg hla.le, hTdef, mul_pow]
      have : la ^ (2 * (q : ℝ)) = la ^ (2 * q) := by
        rw [← Real.rpow_natCast]; push_cast; ring_nf
      rw [this]
      have h1 : H₁ ^ (2 * q) ≠ 0 := pow_ne_zero _ hH.ne'
      field_simp
    have hA' : ∫⁻ x in A a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => lA k r z (Matrix.of x) a) f (A a) (hAm a) T hT (fun x hx => hx.2) (2 * q)).trans ?_
      rw [← key]
      gcongr
      exact hM a
    have hB' : ∫⁻ x in B a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => (lA k r z (Matrix.of x) a)⁻¹) f (B a) (hBm a) T hT (fun x hx => ?_) (2 * q)).trans ?_
      · have hpos : 0 < lA k r z (Matrix.of x) a := hx.1.2
        exact (le_inv_comm₀ hT hpos).2 hx.2.2
      · rw [← key]
        gcongr
        exact hI a
    refine (lintegral_union_le _ _ _).trans ?_
    exact (add_le_add hA' hB').trans (le_of_eq (two_mul _).symm)
  calc ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
          (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS
        ≤ ∫⁻ x, U.indicator f x ∂νS := lintegral_mono fun x => Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    _ = ∫⁻ x in U, f x ∂νS := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in N, f x ∂νS + ∫⁻ x in ⋃ a, (A a ∪ B a), f x ∂νS := lintegral_union_le _ _ _
    _ ≤ 0 + ∑ a : Fin (r + 1), ∫⁻ x in A a ∪ B a, f x ∂νS := by
        gcongr
        · exact (setLIntegral_measure_zero _ _ hG).le
        · exact (lintegral_iUnion_le _ _).trans (le_of_eq (tsum_fintype _))
    _ ≤ ∑ _a : Fin (r + 1), 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hc a
    _ ≤ ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity)]
        gcongr ?_ * _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith

end GlobalTheory.Amp.TailTwo
end
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLengthTailBound_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  atlas_forward_decl GlobalTheory.Amp.TailTwo.tailBd_of_moments
end

section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem size_bound_inv {b v g x Cg Cu CT : ℝ} {r : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  calc x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2) * r) * (b ^ max 2 Cu) ^ (2 * r) := by gcongr
    _ = b ^ ((2 * Cg + 2) * r + max 2 Cu * ((2 * r : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le (max 2 Cu)]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        push_cast
        have := abs_nonneg CT
        nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]

theorem rpow_bridge {b C x : ℝ} {q : ℕ} (hb : 0 ≤ b) : b ^ (2 * C * x * q) = (b ^ (C * x)) ^ (2 * q) := by
  rw [← Real.rpow_mul_natCast hb]; congr 1; push_cast; ring

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem hypTT_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (w : D.what₂.Word) : HypTT D w w := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, -, -, -, -, -, -, -⟩, hDat, -⟩ := hZ
  obtain ⟨-, -, -, -, -, -, -, -, hmod, -⟩ := hDat
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb2 : 2 < large₂.sc.b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hbe
  have hkb : 2 < (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hg : (2 : ℝ) < D.host.g 0 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg1)
  have hg' : 2 < D.host.g 0 := by exact_mod_cast hg
  have hgg : (2 : ℝ) < D.host.g 1 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg2)
  have hgg' : 2 < D.host.g 1 := by exact_mod_cast hgg
  have hp := (D.mem w).A.T_prime
  have h3 : 3 ≤ (D.mem w).A.T := by
    rcases (D.mem w).A.T_prime.two_le.eq_or_lt with h | h
    · exfalso
      have hm := (hmod w).2
      rw [← h] at hm
      have hN : 4 < (D.host.g 0 * D.host.g 1) ^ 2 := by
        have h9 : 9 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul (show 3 ≤ D.host.g 0 from hg') (show 3 ≤ D.host.g 1 from hgg')
        nlinarith
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
    · omega
  exact ⟨hp, hp, h3, h3, Int.ModEq.refl _⟩

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl)
    (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : D.host.rdE ≤ large₂.sc.b := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -⟩, -, -⟩ := hZ
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have h0 : 0 < D.host.rdE := by rw [hrd]; linarith
  have h1 : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
  show D.host.rdE ≤ Real.exp large₂.sc.L
  exact (Real.log_le_iff_le_exp h0).1 (hrdL.trans h1)

end GlobalTheory.TwoSidedMoments
end
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMassGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset GlobalTheory.LowTypeMass
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt_gap (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hRS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hRS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hRS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem weightedMass_bound_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg) (ν : Fin (2 * r + k + 1) → ℤ) (hν0 : n1 ν ≤ q0)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hbd : ∀ (Q : Mx k r) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub),
      PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q →
      (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) →
      ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
        (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd)
    (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w) :
    ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  classical
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hbd' := hbd Q E hQ hE
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) :=
    GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.1 k r lam u b bv ga h q0 R hNum hFam ν hν0
  have hDS := GlobalTheory.isDS_of_isDG hDG
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have hlenv : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) νq :=
    aemeasurable_pi_iff.2 hlen
  rcases eq_or_ne Bd ⊤ with rfl | hBd
  · exact le_top
  have hCB : ENNReal.ofReal Bd.toReal = Bd := ENNReal.ofReal_toReal hBd
  rw [← hCB]
  rw [← hCB] at hbd'
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((Real.sqrt (φ (fun a => lenA k r z (Matrix.of x) a)) * Real.sqrt (dg ν) : ℝ) : ℂ) •
      lb ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ Bd.toReal ENNReal.toReal_nonneg ?_ w hwL hw1
  · simpa only [norm_sq_sqrt_scaled (hφ0 _) hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add, hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_).smul (hmeas (lb ν) hBeL.1 v hv)
    exact (((hφm.comp_aemeasurable hlenv).sqrt).mul_const _).aestronglyMeasurable
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hBc := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (lb ν) hBeL.1.1 hBeL.1.2.1
      hBeL.1.2.2.2 v hv).1
    have hF := measurable_piecewise_mass z hSide.1 hT φ hφm (dg ν) (fun x => lb ν ((R ν).σ x v)) hBc
    have := lintegral_rmul_of_measurable hSide
      (fun x => ENNReal.ofReal (φ (fun a => lenA k r z x a)) * ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ x v)‖ ^ 2))
      hF ?_ hgG
    · have e1 : ∀ x : Formalism.QuantumDeterminants.Mt k r, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
          (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)) =
          ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
            ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) :=
        fun x => ENNReal.ofReal_mul (hφ0 _)
      simp only [e1]
      rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      simp only [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
      rw [ENNReal.ofReal_mul (hφ0 _)]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      simp only [e]
      rw [hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    have hLev := lev_zero_of_wt_gap hH.1 hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
    have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
    exact hbd' ⟨v, hvs⟩ hLev hv1'

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem mass_low_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw =>
    weightedMass_bound_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw

end main

end GlobalTheory.LowTypeMassGap
end
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedMass_highestToLowestKType_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  atlas_forward_decl GlobalTheory.LowTypeMassGap.mass_low_gap
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMomentGap

theorem inv_len_moment_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  have hS' := hS
  obtain ⟨hN, hF, hG, hSF⟩ := hS'
  have hb : 1 ≤ b := by
    obtain ⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
    have e1 := h7 (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e2 := h8 (Fin.last _)
    have e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ e3
    have e5 := neg_abs_le (lam (Fin.last _))
    linarith [e1.2]
  have hdg : 0 < dg ν := (hSF ν hν).2.1
  obtain ⟨m1, -, m3, m4⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq
    (hF ν hν) hG
  refine GlobalTheory.T.weightedMass_highestToLowestKType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν
    (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw
  intro Q E hQ hE v hv hv1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2
  have hv1' : ‖(v : (R ν).H)‖ = 1 := hv1
  simp only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass
  have hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c := by
    filter_upwards [m1] with x hx
    obtain ⟨e1, e2⟩ := GlobalTheory.T.last_majorant_length_sq_ge_and_pos k r z hG.1 hG.2.1 _ hx
    refine ⟨?_, fun c => (e2 c).1⟩
    have := (e2 (Fin.last r)).1
    nlinarith
  have hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq :=
    (((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _
  have key := GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one (Mt k r) νq r q
    (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2)
    (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val))
    (fun c => (m3 _).div (m3 _))
    (fun c => by
      filter_upwards [hpos] with x hx
      exact div_nonneg (hx.2 _).le (hx.2 _).le)
    hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)
    (fun c => by
      have := Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν
        0 (r * q) (by omega) c v hv
      rwa [hv1, one_pow, mul_one] at this)
  have hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [← hpw]
  refine le_trans (lintegral_mono_ae ?_) key
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.1 (hx.2 a).le

end GlobalTheory.InvLenMomentGap
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseMajorantLength_moment_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  atlas_forward_decl GlobalTheory.InvLenMomentGap.inv_len_moment_gap
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMomentsGap

open GlobalTheory.AmpMoments GlobalTheory.TwoSidedMoments

theorem family_through_gap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (ν₀ : Fin (2 * r + k + 1) → ℤ) (R0 : Rep k r) (hN : Num k r lam u b bv ga h q0)
    (hR0 : R0.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν₀ a : ℝ))) (hν₀ : n1 ν₀ ≤ q0) :
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFamG lam q0 R ∧ R ν₀ = R0 := by
  classical
  have hex : DSExistG := hH.1.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  obtain ⟨hN1, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = ν₀ → R = R0) := by
    intro ν
    by_cases h0 : ν = ν₀
    · refine ⟨R0, fun hq => ?_, fun _ => rfl⟩
      subst h0
      exact ⟨hR0.1, hR0.2, h / 2, (hfam ν hq).2.2.1, hN1.2.2.2.2⟩
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC ⟨h / 2, (hfam ν hq).2.2.1, hN1.2.2.2.2⟩
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR ν₀).2 rfl⟩

theorem moment_of_bessel_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ}
    {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν) (q : ℕ) (h1 : n1 ν + (r + 1) * q ≤ q0)
    (h2 : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hν : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) h1
  have hSG := ((GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS)
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  have hDG := hSG.2.1 ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.oneMajorantLength_moment_lowestKType hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν q h1 h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ lenA k r z (Matrix.of x) a ^ (2 * q) := pow_nonneg Metric.infDist_nonneg _
  rw [sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

theorem inv_moment_of_bessel_gap (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ}
    {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}
    {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r} {l : ∀ ν, (R ν).H → Wp} {dg : (Fin (2 * r + k + 1) → ℤ) → ℝ}
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (hT : 1 ≤ Tz k r z) (ν) (q : ℕ) (hν : n1 ν ≤ q0)
    (h2 : r * q ≤ 2 * (2 * r + k + 1) ^ 2) (R0 : Rep k r) (hR : R ν = R0) (B : R0.H → Wp)
    (hB : IsBes R0 z π B) (v : R0.H) (hv : v ≠ 0)
    (hlow : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P ∧
      v ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (fun g => R0.σ (P⁻¹ * g * P)))
    (h0 : l2SG νq (fun g => B (R0.σ g v)) ≠ 0) (ht : l2SG νq (fun g => B (R0.σ g v)) ≠ ⊤) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖B (R0.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂νq ≤
      ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) * l2SG νq (fun g => B (R0.σ g v)) := by
  subst hR
  have hSG := ((GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS)
  obtain ⟨hNum, hFam, hSide, hSF⟩ := id hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  have hDG := hSG.2.1 ν hν
  obtain ⟨hBe, hpos, -⟩ := hSF ν hν
  obtain ⟨-, -, -, hsm, hTK, -, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ (R ν) hDS
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : (R ν).H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hvw : v = ((‖v‖ : ℝ) : ℂ) • w := by
    rw [hw, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwl : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w := by
    obtain ⟨P, hP, hvP⟩ := hlow
    exact ⟨P, hP, hw1, Submodule.smul_mem _ _ hvP⟩
  have hwK : (R ν).KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hwl
  have hvK : (R ν).KFin v := by
    obtain ⟨S, hS1, hS2, hS3⟩ := hwK
    exact ⟨S, hS1, by rw [hvw]; exact S.smul_mem _ hS2, hS3⟩
  have hws : w ∈ (R ν).sm := hTK _ (hKT _ hwK)
  obtain ⟨v₁, hv₁, hl⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq B (l ν) v hDS hgap hOK hSide hB
    hvK h0 ht hBe
  have hnz : NzOn (R ν) (l ν) := ⟨v₁, hTK _ (hKT _ hv₁), hl⟩
  obtain ⟨c, hc⟩ := GlobalTheory.GapLine.bessel_line_gap hH k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) B hDG hSide hBe.1 hnz hB
  have hmass := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν).2 hnz).2 w hws
  have hmom := GlobalTheory.T.inverseMajorantLength_moment_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS hT ν q hν h2 w hwl a
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 m0 m1 hq
  set K : ℝ := (‖v‖ * ‖c‖) ^ 2 / dg ν with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ᵐ x ∂νq, ‖B ((R ν).σ (Matrix.of x) v)‖ ^ 2 = K * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) := by
    filter_upwards [hae] with x hx
    have hxs := hsm _ hx w hws
    have : B ((R ν).σ (Matrix.of x) v) = ((‖v‖ : ℝ) : ℂ) • c • l ν ((R ν).σ (Matrix.of x) w) := by
      conv_lhs => rw [hvw, map_smul]
      rw [hB.2.1 _ _ hxs, hc _ hxs]
    rw [this, norm_smul, norm_smul, Complex.norm_real, norm_norm, hK]
    field_simp
  have e1 : l2SG νq (fun g => B ((R ν).σ g v)) = ENNReal.ofReal K := by
    rw [hw1, one_pow, ENNReal.ofReal_one] at hmass
    rw [← mul_one (ENNReal.ofReal K), ← hmass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [sq_nnnorm, hx, one_mul, ENNReal.ofReal_mul hK0]
  rw [e1, mul_comm (ENNReal.ofReal _) (ENNReal.ofReal K)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hmom _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with x hx
  have hl0 : 0 ≤ (lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) := pow_nonneg (inv_nonneg.2 Metric.infDist_nonneg) _
  rw [sq_nnnorm, hx, ← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hK0]
  congr 1; ring

end GlobalTheory.TwoSidedMomentsGap

namespace GlobalTheory.TwoSidedMomentsGap

open GlobalTheory.AmpMoments GlobalTheory.TwoSidedMoments

theorem two_sided_moments_gap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧
      ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) *
        (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
        ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  intro hH Cg cb Cu cT CT C0
  refine ⟨2 * |Cg| + 2 + |CT| + 10 * max 2 Cu, by positivity, ?_⟩
  intro D large₂ C' Cl hCl hZ τ w W hW A hA q hq
  haveI := FiniteDimensional.complete ℂ W.Wp
  obtain ⟨-, -, hb, hm, -, -, -, hmk, hv, -, hka, hvb, hg, hgb, hCg, -, hT, -⟩ :=
    GlobalTheory.Amp.RangeModel.sizes_of D large₂ C' Cl Cg cb Cu cT CT C0 (rd_le_b D large₂ C' Cl Cg cb Cu cT CT C0 hCl hZ) hZ
  have hTT := hypTT_self D large₂ C' Cl Cg cb Cu cT CT C0 hZ w
  have hb1 : 1 ≤ large₂.sc.b := by have := Real.add_one_le_exp 1; linarith
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  obtain ⟨hNum, -, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w (uOne D w τ) (fun i => by
    have := i.isLt
    simp only [uOne]
    rw [dif_pos ⟨by omega, by omega⟩]; rfl)
  set ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ := 0 with hν0
  have e0 : (fun i => lamD D τ i + (ν i : ℝ)) = lamD D τ := funext fun i => by simp [hν0]
  have hn0 : n1 ν = 0 := by simp [hν0, n1]

  have hm1 : D.R.rS + 1 ≤ D.R.m := by omega
  have hkm : D.R.k * D.R.m ^ 4 ≤ D.R.k * D.R.k := Nat.mul_le_mul_left _ hmk
  have hq1 : (D.R.rS + 1) * q ≤ D.R.k * D.R.m ^ 4 :=
    calc (D.R.rS + 1) * q ≤ D.R.m * (D.R.k * D.R.m ^ 3) := Nat.mul_le_mul hm1 hq
      _ = D.R.k * D.R.m ^ 4 := by ring
  have hr1 : n1 ν + (D.R.rS + 1) * q ≤ D.R.k * D.R.m ^ 5 := by
    rw [hn0, zero_add]
    exact hq1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num)))
  have hr2 : (D.R.rS + 1) * q ≤ 2 * (2 * D.R.rS + D.R.k + 1) ^ 2 := by
    refine hq1.trans (hkm.trans ?_)
    nlinarith
  have hr3 : D.R.rS * q ≤ 2 * (2 * D.R.rS + D.R.k + 1) ^ 2 :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans hr2
  let R0 : Rep D.R.k D.R.rS := { H := A.H, σ := A.σ }
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6, hA7, hA8, hA9, -⟩ := hA
  rw [← heps] at hA2 hA7
  have hDS : R0.IsDS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun i => lamD D τ i + (ν i : ℝ)) := by
    rw [e0]; exact ⟨hA1, hA2⟩
  have hA7' : ∃ P, PI.UpqRep.IsCayleyU D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) P ∧
      A.v0 ∈ PI.UpqRep.lowKSub (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun a => lamD D τ a + (ν a : ℝ))
        (fun g => R0.σ (P⁻¹ * g * P)) := by
    rw [e0]; exact hA7
  obtain ⟨R, hFamG, hR⟩ := family_through_gap hH _ _ _ _ _ _ _ _ _ ν R0 hNum hDS (by rw [hn0]; exact Nat.zero_le _)
  have hFam : IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R := fun ν' hν' => GlobalTheory.isDS_of_isDG (hFamG ν' hν')

  set c : ℝ := 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) with hc
  have hc2 : c = 2 * (Real.pi / D.host.v / gg D) := by rw [hc, hka, gg]; ring
  have hc0 : 0 < c := by rw [hc2]; have := Real.pi_pos; positivity
  obtain ⟨t, htG, htN, htz, hts⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter D.R.k D.R.rS (c : ℂ) (by exact_mod_cast hc0.ne')
  choose s hs0 hs1 hs2 hs3 using hts
  have htd : IsUnit t.det := Matrix.isUnit_det_of_right_inverse (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv htG).2.1
  obtain ⟨U, U', l, l', dg, hS, -⟩ := GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w 1 W hTT one_pos hW t htG
    htN (fun z hz => (htz z hz).2) R hFam
  obtain ⟨-, -, hz, -, hTz, -, hG, -, -, -, -, -, hQ, -⟩ := hW
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hS.2.2.1
  have hSide : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨g1, g2, g3, g4, g5, haar_of_conj htd htN g6, g7, hQ⟩
  have hB := (((GlobalTheory.BesselMoveGap.bessel_move_gap hH _ _ W.Wp W.z W.π U (c : ℂ) W.μW W.μN W.μG W.νS t htG htN
    (htz _ hz).2.1 (htz _ hz).2.2 hSide).2 R0 (GlobalTheory.TensCompare.isURepOn_of_isDS hDS)).1 A.B).1 (isBesselMapSm_of hA3)
  obtain ⟨hmul, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 _ _ _ _ R0 hDS
  obtain ⟨m0, m1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts g5 g6
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot g7.2.2.1 m0 m1 g8
  set νq := W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j with hνq
  have hpt : ∀ᵐ x ∂νq, A.Φ (t * Matrix.of x) = A.B (R0.σ t (R0.σ (Matrix.of x) A.v0)) := by
    filter_upwards [hae] with x hx
    exact congrArg A.B (hmul t htG _ hx A.v0)
  have e1 : l2SG W.νS A.Φ = l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) := by
    unfold l2SG
    rw [lintegral_translate W.νS t htd]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx]; rfl
  have hfr : 0 < Module.finrank ℂ W.Wp := by
    obtain ⟨_, _, -, hρ⟩ := g3
    haveI := hρ.1
    exact Module.finrank_pos
  have hne0 : l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) ≠ 0 := by
    rw [← e1, hA9]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hneT : l2SG νq (fun g => A.B (R0.σ t (R0.σ g A.v0))) ≠ ⊤ := by
    rw [← e1, hA9]; exact ENNReal.ofReal_ne_top
  have hTz1 : 1 ≤ Tz D.R.k D.R.rS W.z := by
    rw [hTz]; unfold Tr; exact_mod_cast (le_trans (by norm_num) hTT.2.2.1)
  have hCH : (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ) ≤ (2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ) := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Cg)]
  have hpow : (large₂.sc.b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) ≤
      (large₂.sc.b ^ ((2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hb0 _) (Real.rpow_le_rpow_of_exponent_le hb1 hCH) _
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  have hsa : ∀ a, ‖s a‖ ≤ max (Real.pi / D.host.v / gg D) (Real.pi / D.host.v / gg D)⁻¹ ^ D.R.rS ∧
      ‖s a‖⁻¹ ≤ max (Real.pi / D.host.v / gg D) (Real.pi / D.host.v / gg D)⁻¹ ^ D.R.rS := fun a => by
    have h1 := hs1 a
    have h2 := hs2 a
    rw [Complex.norm_real, Real.norm_of_nonneg hc0.le, ← inv_div c 2, hc2,
      mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))] at h1 h2
    exact ⟨h1, h2⟩
  constructor
  · intro a
    have key := moment_of_bessel_gap hH hS ν q hr1 hr2 R0 hR _ hB A.v0 hA6 hA7' hne0 hneT a
    have hsz := size_bound (q := q) (Cu := Cu) hb hv hvb hg hgb hCg (T := Tz D.R.k D.R.rS W.z) (CT := CT)
      (r := D.R.rS) (by rw [hTz]; have := hT w; rw [hm] at this; exact_mod_cast this) (norm_nonneg (s a)) (hsa a).1
    rw [rpow_bridge hb0, ← hm'] at hsz
    rw [e1]
    refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hsz.trans hpow)) _)
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
    rw [lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      ← lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
    rfl
  · intro a
    have key := inv_moment_of_bessel_gap hH hS hTz1 ν q (by rw [hn0]; exact Nat.zero_le _) hr3 R0 hR _ hB A.v0 hA6
      hA7' hne0 hneT a
    have hsz := size_bound_inv (Cu := Cu) (CT := CT) hb hv hvb hg hgb hCg (r := D.R.rS)
      (inv_nonneg.2 (norm_nonneg (s a))) (hsa a).2
    rw [← hm'] at hsz
    have hsz2 : (‖s a‖⁻¹) ^ (2 * q) * ((large₂.sc.b ^ max 2 Cu) ^ (2 * D.R.rS)) ^ (2 * q) ≤
        (large₂.sc.b ^ ((2 * |Cg| + 2 + |CT| + 10 * max 2 Cu) * (D.R.m : ℝ))) ^ (2 * q) := by
      rw [← mul_pow]
      exact (pow_le_pow_left₀ (by positivity) hsz _).trans hpow
    rw [e1]
    refine le_trans ?_ (mul_le_mul_left (ENNReal.ofReal_le_ofReal hsz2) _)
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    refine le_trans (le_of_eq ?_) (mul_le_mul_right key _)
    rw [lintegral_translate W.νS t htd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with x hx
    rw [← hx, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, ← mul_inv,
      ← lenA_mul W.z t (Matrix.of x) s hs0 (fun b => hs3 b _ hz), BranchingSupport.TensInh.lenA_eq_lA]
    rfl

end GlobalTheory.TwoSidedMomentsGap
end
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLength_twoSidedMoments_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CH : ℝ, 0 ≤ CH ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w (W : LocW D.R.k D.R.rS), GoodW D τ w w 1 W → ∀ A : LocS W, GoodS D (lamD D τ) A → ∀ q : ℕ, q ≤ D.R.k * D.R.m ^ 3 → MomBd W.z W.νS A.Φ q (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧ ∀ a : Fin (D.R.rS + 1), ∫⁻ x, ENNReal.ofReal ((lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤ ENNReal.ofReal ((large₂.sc.b ^ (CH * (D.R.m : ℝ))) ^ (2 * q)) * l2SG W.νS A.Φ := by
  atlas_forward_decl GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TypeAsm

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem tailBd_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  intro D τ w θ lam q H₁ h W hW A hA
  exact h (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA)

end GlobalTheory.TypeAsm
end
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  atlas_forward_decl GlobalTheory.TypeAsm.tailBd_primed_of_unprimed
end

section
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TypeAsm.TailTopGap

theorem tailP_of_gap : GlobalTheory.GapIn.Hyp → TailP := by
  intro hH Cg cb Cw cT CT C0 _ _
  obtain ⟨CH, hCH, hmom⟩ := GlobalTheory.T.majorantLength_twoSidedMoments_largeGap hH Cg cb Cw cT CT C0
  refine ⟨CH, hCH, fun C₁ => ⟨0, max 1000 (C₁ : ℝ), fun C' Cl _ hCl D large₂ _ hK hTr => ?_⟩⟩
  have hZ : HypZ D large₂ C' Cl Cg cb Cw cT CT C0 := hK.1
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_left _ _) hCl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hK.1.1

  have hC₁m : C₁ ≤ D.R.m := by
    have h : (C₁ : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) (le_trans hCl hClm)
    exact_mod_cast h
  have hrS : D.R.rS ≤ D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hq : C₁ * D.R.k * D.R.rS ≤ D.R.k * D.R.m ^ 3 := by
    have h2 : C₁ * D.R.rS ≤ D.R.m ^ 3 :=
      calc C₁ * D.R.rS ≤ D.R.m * D.R.m := Nat.mul_le_mul hC₁m hrS
        _ ≤ D.R.m * D.R.m * D.R.m := Nat.le_mul_of_pos_right _ (by omega)
        _ = D.R.m ^ 3 := by ring
    calc C₁ * D.R.k * D.R.rS = D.R.k * (C₁ * D.R.rS) := by ring
      _ ≤ D.R.k * D.R.m ^ 3 := Nat.mul_le_mul_left _ h2
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hH1 : 0 < large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.rpow_pos_of_pos hb _

  have hTrpos : ∀ w, 0 < Tr D w := by
    intro w
    have hk : 0 ≤ Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) := (even_two_mul _).pow_nonneg _
    by_contra hneg
    push_neg at hneg
    have h0 : Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hk
    linarith [hTr w]
  have hv0 : 0 < D.host.v := by linarith
  intro τ u W hW A hA

  have side : ∀ W' : LocW D.R.k D.R.rS, GoodW D τ u u 1 W' → ∀ A' : LocS W', GoodS D (lamD D τ) A' →
      TailBd W'.z W'.νS A'.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) := by
    intro W' hW' A' hA'
    obtain ⟨hM, hI⟩ := hmom D large₂ C' Cl h1000 hZ τ u W' hW' A' hA' _ hq
    obtain ⟨hzW, -, -, -, -, hG, hWH, -, hN, hQ, -, -, hcont, -, -⟩ :=
      (GlobalTheory.T.amplitude_one_side_of_good_local_data D τ u u 1 W' (lamD D τ) A' hv0 one_pos (hTrpos u) (hTrpos u) hW' hA').1
    have hnull : W'.νS {x | Matrix.of x ∉ GG D.R.k D.R.rS} = 0 := by
      have hf := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWH hN
      exact ae_iff.mp (Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hf.1 hf.2 hQ)
    exact GlobalTheory.T.majorantLengthTailBound_of_moments D.R.k D.R.rS W'.z W'.νS A'.Φ _ _ hzW hH1 hnull hcont hM hI

  exact ⟨side W hW A hA, GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed D τ u 1 (lamD D τ) _ _ side W hW A hA⟩

end GlobalTheory.TypeAsm.TailTopGap
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDataTailBound_closedForm_largeGaps : GlobalTheory.GapIn.Hyp → TailP := by
  atlas_forward_decl GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap
end

section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termAmplitudeFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Cs C : ℝ) (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) :
    0 ≤ k2a large₂ CH Cs C j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := le_trans zero_le_one (one_le_sigma_product _ j δ)
  unfold k2a
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _)
    (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)
  unfold Formalism.MainNotions.S.Cnt.Hb
  exact Real.rpow_nonneg hb.le _

theorem typeBound_of_amplitude_pairs : AmpP → PairsP → TypeP := by
  intro hAmp hPairs Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hA⟩ := hAmp Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩ := hPairs Cg cb Cw cT CT C0 CH hCH
  refine ⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩
  obtain ⟨C₀, hC₀, hA2⟩ := hA Cs (by linarith)
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨C'₂, Cl₂, hA3⟩ := hA2 C hC
  refine ⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩
  have amp := hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc
  have pairs := hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc
  intro j' hj' j'' hj'' δ' δ'' S hS
  have hC0 : 0 ≤ C := le_trans hC₀ hC
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u := Real.mul_self_sqrt hdpi
  have ha' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'
  have ha'' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''
  have hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') :=
    mul_nonneg hdpi (mul_nonneg ha' ha'')
  have hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
    intro p hp
    obtain ⟨hmem, hj1, hj2, hl1, hl2⟩ := hS p hp
    have h1 := amp p.1 hmem.1
    have h2 := amp p.2 hmem.2.1
    rw [hj1, hl1] at h1
    rw [hj2, hl2] at h2
    calc ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
        ≤ (Formalism.L2.SG.TermOp.wt p.1 * Real.sqrt (dpiC X u) * (omT p.1 * k2a large₂ CH Cs C j' δ')) *
          (Formalism.L2.SG.TermOp.wt p.2 * Real.sqrt (dpiC X u) * (omT p.2 * k2a large₂ CH Cs C j'' δ'')) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u)) * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
          ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by ring
      _ = _ := by rw [hsq]
  calc ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
      ≤ ∑ p ∈ S, dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := Finset.sum_le_sum hterm
    _ = dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ∑ p ∈ S, ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
      rw [Finset.mul_sum]
    _ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) :=
      mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0
    _ = _ := by ring

end GlobalTheory.TypeAsm
end
end

section
section
namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  atlas_forward_decl GlobalTheory.TypeAsm.TopGap.typeBound_of_gap
end

section
namespace GlobalTheory

theorem rowsPos_typeP : Formalism.L2.SG.RowsPos.TypeP :=
  GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2

end GlobalTheory
end
