import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AmplitudeOrbitalIntegral
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.SmoothIrreducibility.SmoothVectorsIrreducible
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.SchurRelationsDiscreteSeries
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AIsL
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.AutomorphicTheory.RankOneTori.KDense
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

section
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec

namespace BM

section Core

variable {k r : ℕ}

theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x := by
  obtain ⟨B, hB, hWB⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W hc1 he1 hr1 hl1 hl1'
  obtain ⟨B0, hB0, hW0B⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W0 hc2 he2 hr2 hl2 hl2'
  rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB hB0
  obtain ⟨a, b, hab, hlin'⟩ := hM1 k r ε lam h H σ z (fun _ => c) u Vp π hok.1 hg hok.2.1 hl hds hz hT (fun _ => hc) hπ
    B B0 ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B).1 hB) ((Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff z _ σ π B0).1 hB0)
  have hlin : ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B v + b • B0 v = 0 := fun v hv => hlin' v hv
  have hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ :=
    fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    obtain ⟨x0, hx0U, hx0W⟩ := hx0
    have h1 := hlin (σ x0 w) (hsm x0 hx0U)
    rw [ha, zero_smul, zero_add] at h1
    have h2 : B0 (σ x0 w) = 0 := (smul_eq_zero.1 h1).resolve_left hb
    exact hx0W (by rw [hW0B x0 hx0U, h2])
  · refine ⟨-(b / a), fun x hx => ?_⟩
    have h1 := hlin (σ x w) (hsm x hx)
    rw [hWB x hx, hW0B x hx]
    have : a • B (σ x w) = -(b • B0 (σ x w)) := eq_neg_of_add_eq_zero_left h1
    calc B (σ x w) = a⁻¹ • (a • B (σ x w)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = -(b / a) • B0 (σ x w) := by
          rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Core

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

section Main

variable {k r : ℕ}

theorem locUniq_gen (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists)
    (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameJ (eps48 k r) e f wf (z0v T z))
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hDS : IsDS (eps48 k r) (lam48 k r v b) σ)
    {w : H} (hw : IsLowUnit (eps48 k r) (lam48 k r v b) σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    {πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)} (hπ : IsHCTypeU k u πl)
    {μS ν : Measure (Formalism.REAL.UJ (eps48 k r))} (hS : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS)
    (hQ : IsLocQuot μS ν)
    {W : Formalism.REAL.UJ (eps48 k r) → Vl} (hWc : Continuous W)
    (hWe : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h * m →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG (eps48 k r)) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ∂ν
      < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (eps48 k r) → ℂ) (Ω : Set (Formalism.REAL.UJ (eps48 k r))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG (eps48 k r)) = W x := by
  obtain ⟨P0, hP0⟩ := Formalism.MainNotions.S.Inh.exists_isCayleyU_eps48 k r hk
  have hCP : CayPair (eps48 k r) P0 (Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r)) := ⟨hP0.1.2, rfl⟩
  generalize hB0 : Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r) = B0 at hCP
  have hinv : P0⁻¹ = B0 := Matrix.inv_eq_left_inv hCP.BP
  have hσB1 : (fun g => (fun M => σ (P0 * M * B0)) (P0⁻¹ * g * P0)) = σ := by
    funext g
    simp only [hinv]
    congr 1
    simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]
    rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hDSB : IsDSHpk k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) := ⟨P0, hP0, by rw [hσB1]; exact hDS⟩
  have hwB : IsLowUnitH k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) w := ⟨P0, hP0, by rw [hσB1]; exact hw⟩
  have hcc0 : ((4 * Real.pi / gg : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * Real.pi / gg := by positivity
    exact_mod_cast this.ne'
  have hTz : 0 < Tz k r (zBv k r T) := by rw [Tz_zB hT.le]; exact hT
  have hS48 : RealPlaceNumericalSetting k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b :=
    ⟨hk, hke, inWb_zB T, hTz, fun _ => hcc0, hu, hl, hI, hH, hGap⟩
  have hπB := hcTypeW_piB hF hT.le hπ
  have hG := isHaarOn_G hCP
  have hSB := isHaarOn_S hF hS
  have hQB := isQuotMeas_B hF hCP hQ
  obtain ⟨μW, μN, hW, hN, hWfin, hNc⟩ := WlocSk.haar_measure_unipotent_nilradical k r (zBv k r T) (inWb_zB T) hTz
  obtain ⟨cS, hcS0, hcSt, hP⟩ := WlocSk.product_decomposition_holds k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b H
    (fun M => σ (P0 * M * B0)) Vl (piB (eps48 k r) e f wf (z0v T z) πl) w _ _ _ μW μN
    ⟨hS48, hDSB, hπB, hwB, hG, hSB, hQB, hW, hN, hWfin, hNc⟩
  have hmuS : Formalism.MainNotions.S.muS μW μN =
      cS • (μS.map (cM (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)))) := hP
  have hQ' : IsQuotMeas ((Formalism.REAL.muG (eps48 k r)).map (cM B0 P0)) (Formalism.MainNotions.S.muS μW μN)
      (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) := by
    intro g hg
    rw [hQB g hg, hmuS]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hcSt, ← mul_assoc, ENNReal.inv_mul_cancel hcS0 hcSt, one_mul]
  have hS' : IsHaarOn (Sset k r (zBv k r T)) (Formalism.MainNotions.S.muS μW μN) := by
    rw [hmuS]; exact isHaarOn_smul hSB hcS0 hcSt
  obtain ⟨W0, hc0, he0, hr0, -, hL20, hwt0, α, Ω, a, hΩc, h1Ω, hΩU, hαm, hαs, hαb, hαr⟩ :=
    hWl hB hCW k r (zBv k r T) _ u v b hS48 H _ hDSB Vl (piB (eps48 k r) e f wf (z0v T z) πl) hπB w hwB _ _ _
      hG hS' hQ'
  have hpsi : Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ) =
      psiGen k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) := Formalism.L2.SG.LitS.psi_eq_psiGen _ _ _ _
  have he0' : IsSPsiEquiv (zBv k r T) (Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ))
      (piB (eps48 k r) e f wf (z0v T z) πl) W0 := by rw [hpsi]; exact he0
  have embX := cM_measEmb (ε := eps48 k r) (A := Qi (eps48 k r) e f wf (z0v T z)) (B := P0)
    (A' := Qm e f wf (z0v T z)) (B' := B0) (Qm_mul_Qi hF) hCP.PB
  have embG := cM_measEmb (ε := eps48 k r) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have hXU : ∀ x : Formalism.REAL.UJ (eps48 k r),
      (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r) := cX_mem_UH hF hCP

  have hl2eq : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) =
      cS⁻¹ * ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν := by
    unfold l2SG
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
    congr 1
    refine lintegral_congr fun x => ?_
    show (‖WB hF hCP W (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = ‖W x‖ₑ ^ 2
    rw [WB_cM]; rfl
  have hcSi0 : cS⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hcSt
  have hcSit : cS⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hcS0
  have hl2ne : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) ≠ 0 := by
    rw [hl2eq]; exact mul_ne_zero hcSi0 hL0
  have hl2lt : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) < ⊤ := by
    rw [hl2eq]; exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSit) (lt_top_iff_ne_top.2 hLt)

  have hx0 : ∃ x0 ∈ UH (Hpk k r), W0 x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) W0 = 0 := by
      unfold l2SG
      rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
      have hz0 : ∀ x : Formalism.REAL.UJ (eps48 k r),
          (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = 0 := by
        intro x; rw [hcon _ (hXU x)]; simp
      simp only [hz0, lintegral_zero, mul_zero]
    rw [hL20] at this
    exact one_ne_zero this
  obtain ⟨a', hprop⟩ := besselUniq_core hBW hM1 hl hDSB hga hok (inWb_zB T) hTz hcc0 hπB hwB (lowSmoothSK hDSB hwB)
    hG hW hN hQ' (WB_continuousOn hF hCP hWc) (WB_equiv hF hCP (Qm_zB hT z) hgg hWe) (WB_reprod hF hCP σ w hWr)
    hl2ne hl2lt hc0 he0' hr0 (by rw [hL20]; exact one_ne_zero) (by rw [hL20]; exact ENNReal.one_lt_top) hx0
  have hWeq : ∀ x : Formalism.REAL.UJ (eps48 k r),
      W x = a' • W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
    intro x; rw [← hprop _ (hXU x), WB_cM]
  refine ⟨?_, ?_⟩
  ·
    have hc : 0 ≤ opn (Qm e f wf (z0v T z)) * opn B0 :=
      mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
    have hN : 0 ≤ N1H k r := by unfold N1H; positivity
    set K : ℝ≥0∞ := ‖a'‖ₑ * ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) with hKdef
    have hpt : ∀ x, ‖W x‖ₑ *
        ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
        K * (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
          ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
      intro x
      have h0 : 0 ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have h0' : 0 ≤ nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have hle := nuLoc_le hF hCP (zBv k r T) x
      rw [hWeq x, enorm_smul, hKdef]
      have h2 : ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
          ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc h0']
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hle hN)
      calc ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r)
          ≤ ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            (ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
            gcongr
        _ = _ := by ring
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)) ?_
    have h3 := hwt0
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map] at h3
    have h4 : ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν =
        cS * (cS⁻¹ * ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcS0 hcSt, one_mul]
    rw [h4]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSt) h3
  ·
    refine ⟨fun g => α (cM B0 P0 g), cM B0 P0 ⁻¹' Ω, a, (cM_closedEmb hCP.PB hCP.PB).isCompact_preimage hΩc, ?_,
      hαm.comp embG.measurable, fun y hy => hαs _ hy, fun y => hαb _, ?_⟩
    · show Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) ∈ Ω
      have : Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) = (1 : Mat k r) := by
        show B0 * uMat 1 * P0 = 1; rw [uMat_one', Matrix.mul_one, hCP.BP]
      rw [this]; exact h1Ω
    · intro x
      obtain ⟨hint, hval⟩ := hαr _ (hXU x)
      have hint2 := embG.integrable_map_iff.mp hint
      have hprod : ∀ g : Formalism.REAL.UJ (eps48 k r), (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
          Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 (x * g)) :=
        fun g => cMprod hCP _ x g
      have hpt : ∀ g : Formalism.REAL.UJ (eps48 k r), α (cM B0 P0 g) • W (x * g) =
          a' • (α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
            Matrix.of (cM B0 P0 g))) := by
        intro g
        rw [hprod, hWeq, smul_comm]
        rfl
      refine ⟨(hint2.smul a').congr (ae_of_all _ fun g => (hpt g).symm), ?_⟩
      rw [integral_congr_ae (ae_of_all _ hpt), integral_smul]
      have h5 : ∫ g, α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) :
          Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g)) ∂(Formalism.REAL.muG (eps48 k r)) =
          W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
        rw [← hval]
        unfold rconv
        rw [embG.integral_map]
      rw [h5, ← hWeq]

end Main

theorem locUniq_n (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hHN : LocHNProps)
    {k r n : ℕ} (hn : n = 2 * r + k + 1) (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    (ε : Fin n → Bool) (hε : ∀ i, ε i = eps48 k r (Fin.cast hn i))
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0)
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (lam : Fin n → ℝ) (hlam : ∀ i, lam i = lam48 k r v b (Fin.cast hn i))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    (πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)) (hπ : IsHCTypeU k u πl)
    (μS ν : Measure (Formalism.REAL.UJ ε))
    (hS : SigmaFinite μS ∧ μS ≠ 0 ∧
      μS {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}ᶜ = 0 ∧
      ∀ s ∈ {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}, μS.map (fun x => s * x) = μS)
    (hQ : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, F (s * x) ∂μS) ∂ν)
    (W : Formalism.REAL.UJ ε → Vl) (hWc : Continuous W)
    (hWe : ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → ∀ h : Formalism.REAL.UJ ε,
      ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) → ∀ x,
      W (m * h * x) = psiR ε gg e f z (uMat (m * h)) • πl (fun a b => hJ ε (wf a) (uMat h *ᵥ wf b)) (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) (N : ℝ) (hN : N ≤ N1H k r) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal
        ((⨅ t : {s : Formalism.REAL.UJ ε | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ ε) * x))) ^ N) ∂ν < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG ε) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG ε) = W x := by
  subst hn
  have hε' : ε = eps48 k r := funext fun i => by rw [hε i]; rfl
  subst hε'
  have hlam' : lam = lam48 k r v b := funext fun i => by rw [hlam i]; rfl
  subst hlam'
  have hF := isFrameJ_of (ε := eps48 k r) e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  have hP := hHN k r (eps48 k r) e f wf (z0v T z) z _ hF hc rfl
  have heq : HNset (eps48 k r) e f wf (z0v T z) (zBv k r T) =
      {s | ∃ m ∈ {g : Formalism.REAL.UJ (eps48 k r) | InN (eps48 k r) e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ (eps48 k r) | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧
          uMat g *ᵥ z = z}, s = m * h} := Set.ext fun s => HNset_eq_NH hHN hT hF s
  have hS' : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS := by
    obtain ⟨h1, h2, h3, h4⟩ := hS
    exact ⟨h1, h2, by rw [heq]; exact h3, fun s hs => h4 s (heq ▸ hs)⟩
  have hz : (Qm e f wf (z0v T z)) *ᵥ (zBv k r T) = z := Qm_zB hT z
  have hzB0 := inWb_zB (k := k) (r := r) T
  have hWe' : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h' ∈ UWset k r (zBv k r T), ∀ m' ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h' * m' →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h' (W x) := by
    intro s x h' hh' m' hm' hsm
    set sh : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hh'.1) with hsh
    set sm : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hm'.1) with hsm'
    have hush : uMat sh = Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have husm : uMat sm = Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have hfix : (∀ a, uMat sh *ᵥ e a = e a) ∧ (∀ a, uMat sh *ᵥ f a = f a) ∧ uMat sh *ᵥ z = z := by
      rw [hush]; exact rev_UW hF hz hh'
    have hNm : InN (eps48 k r) e z (uMat sm) := by rw [husm]; exact rev_N hF hz hzB0 hm'
    have hs_eq : s = sh * sm := by
      apply Subtype.ext; apply Units.ext
      show uMat s = uMat sh * uMat sm
      rw [hush, husm]
      have e1 : uMat s = Qm e f wf (z0v T z) * (Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z)) *
          Qi (eps48 k r) e f wf (z0v T z) := by
        simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
        rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
      rw [e1, hsm]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (Qm e f wf (z0v T z) * h') (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)),
        Qi_mul_Qm hF, Matrix.mul_one]
    have hnn : InN (eps48 k r) e z (uMat (sh * sm * sh⁻¹)) := hP.2.2.2 sh hfix sm hNm
    have hs2 : s = sh * sm * sh⁻¹ * sh := by rw [hs_eq]; group
    rw [hs2, hWe _ hnn sh hfix x, ← hs2]
    unfold piB
    rw [hush]
  obtain ⟨hwt, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩ := locUniq_gen hBW hM1 hB hCW hWl hk hke hT hgg hF hu hl hI
    hH hGap hga hok hDS hw hπ hS' hQ hWc hWe' hWr hL0 hLt
  refine ⟨?_, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩
  have hn0 : 0 < 2 * r + k + 1 := by omega
  have hne1 : Nonempty {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} := ⟨⟨1, inS_one⟩⟩
  have hne2 : Nonempty (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) := by
    refine ⟨⟨1, ?_⟩⟩
    rw [heq]
    exact ⟨1, hP.2.2.1.1, 1, fix_one, (one_mul 1).symm⟩
  have hge1 : ∀ x, 1 ≤ ⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)) := fun x =>
    le_ciInf fun t => Formalism.L2.SG.WuDecayPf.one_le_opn hn0 _
  have hle : ∀ x, (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ≤
      nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x := by
    intro x
    refine le_ciInf fun t => ?_
    have ht : InS e z (uMat (t : Formalism.REAL.UJ (eps48 k r))) := inS_of_HNset hF hz hzB0 ⟨_, rfl⟩ t.2
    exact ciInf_le (f := fun t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} =>
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)))
      ⟨0, by rintro _ ⟨i, rfl⟩; exact Formalism.L2.SG.WuDecayPf.opn_nonneg _⟩ ⟨t, ht⟩
  have hN1 : 0 ≤ N1H k r := by unfold N1H; positivity
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hwt
  gcongr ‖W x‖ₑ * ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N
      ≤ (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
          opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N1H k r :=
        Real.rpow_le_rpow_of_exponent_le (hge1 x) hN
    _ ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r :=
        Real.rpow_le_rpow (by linarith [hge1 x]) (hle x) hN1

def LocUniqStep : Prop :=
  BesselNVGap → CoefWeightedLoc → WlocExists → Formalism.L2.SG.LocWSOf.BesselOfW → CompanionTheory.Lime.BM.UniqGap →
    ∀ (D : Formalism.BasicNotions.D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
      (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ v (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v), Continuous W → LocEquivW X u v W → LocReprodW X u v W →
        ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ 0 → ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ ⊤ → LocConcl X u v (νl v) W

theorem local_uniqueness_reduction : LocUniqStep := by
  intro hB hCW hWl hBW hM1 D hG X u μS νl C hQW v W hWc hWe hWr hL0 hLt
  obtain ⟨-, -, hloc, -⟩ := hQW
  obtain ⟨hSv, hQv⟩ := hloc v
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hN1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by rw [dimS D]; exact hG.1
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hgg : 0 < X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have R := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    have := R (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b => by
    have := R (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => by
      have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) := by
    have := R (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
    rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hw1 := X.wfr_on u v
  have hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

  have hu := Formalism.MainNotions.uS_hc D u (X.pl v)
  have hl : Formalism.QuantumDeterminants.IsHCParam (lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))) := by
    rw [Formalism.MainNotions.lambda_highest_weight_eq]; exact Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (X.pl v))
  have hm := Formalism.MainNotions.two_rS_add_two D
  have hI : InterlacingCondition D.R.k D.R.rS (Formalism.MainNotions.S.uS D u (X.pl v)) (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) := by
    refine ⟨fun i => ?_, fun h => ?_⟩
    · have h1 := (D.hcW u (X.pl v)).u_gt_v i
      have h2 := (D.hcW u (X.pl v)).v_gt_u i
      rw [D.hcW_v u (X.pl v)] at h1 h2
      simp only [Formalism.MainNotions.v48, Formalism.MainNotions.S.uS]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · have h1 := (D.hcW u (X.pl v)).u_last_gt h (by omega)
      rw [D.hcW_b u (X.pl v)] at h1
      simp only [Formalism.MainNotions.b48, Formalism.MainNotions.S.uS]
      have e : (Fin.cast hm ⟨0, by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := rfl
      rw [e]
      exact_mod_cast h1
  have hH := Formalism.MainNotions.LeviCoordinates.halfInt_of_integrality _ _ _ _ _ hu hl
  have hGap := gapBig_of_gapHyp D hG (X.pl v)
  have hga := Formalism.MainNotions.gap_at_least_of_low_gap D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) _ hk hl.1
    (lowGap_of_gapHyp D hG (X.pl v))
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (16 * (D.R.r : ℝ) ^ 19) := by
    have := gapOK_of_big D.R.k D.R.rS hk hN1801
    rwa [dimS D] at this

  have hNH : NHloc X u v = {s | ∃ m ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) (uMat g)}, ∃ h ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) |
        (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)}, s = m * h} := by
    unfold NHloc; rw [Hloc_eq]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := hSv
  rw [hNH] at h3 h4

  have hWe' : ∀ m : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (uMat m) → ∀ h : Formalism.REAL.UJ (X.B.I.ε v),
      ((∀ a, uMat h *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat h *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat h *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) → ∀ x,
      W (m * h * x) = psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
        (rv X.B.I v (X.zR u)) (uMat (m * h)) •
        X.piLoc u v (fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b)) (W x) := by
    intro m hm h hh x
    have hh' : h ∈ Hloc X u v := by rw [Hloc_eq]; exact hh
    have hmat : matW X.B.I (X.wfr u v) v (single X v h) =
        fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b) := by
      funext a b; simp [matW, single]
    rw [hWe m hm h hh' x, hmat]
    rfl
  have key := locUniq_n hBW hM1 hB hCW hWl Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) hk D.R.k_even hT hgg
    (X.B.I.ε v) (eps_cast X v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (X.wfr u v) hee hff hef hez hfz hzz hw1 hew hfw hzw hu hl hI hH hGap hga hok
    (X.B.lam v) (lam_cast X v) (X.B.σ v) (X.ds v) (X.B.w v) (X.low v) (X.piLoc u v) (X.piLoc_type u v)
    (μS v) (νl v) ⟨h1, h2, h3, h4⟩ hQv W hWc hWe' hWr hL0 hLt (N1 X) (first_count_le_log X)
  exact key

theorem locDecayStep_of (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : CompanionTheory.Lime.BM.UniqGap)
    (hR : LocReprodStep) (hU : LocUniqStep) : LocDecayStep := by
  intro D hG X u μS νl C hQ v
  exact hU hB hC hW hBW hM1 D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v)
    (fun m hm h hh x => locEquiv X u v m hm h hh x) (hR D hG X u μS νl C hQ v)
    (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2

theorem wuDecay_gap (hM1 : CompanionTheory.Lime.BM.UniqGap) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hQK : QuotProdK) (hNU : NUnimodLoc) (hS : LocScalarStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecayOfGap_of_steps hC (quotAll_of hQK locHNProps_holds hNU)
    (locDecayStep_of hB hC hW (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_gap hM1) hM1 (locReprodStep_of hS) local_uniqueness_reduction)

end BM

end Formalism.L2.SG.Pf.WuDec
end
end

section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Closed.BM

theorem CoefWeightedLoc_holds : CoefWeightedLoc := ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

theorem BesselNVGap_holds : BesselNVGap := Formalism.L2.SG.BesselDiscreteSeries.besselNVGap

theorem WlocExists_holds : WlocExists := scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

theorem NUnimodLoc_holds : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  have h := n_unimodular_local
  intro k r ε e f wf z0 z c hF hc hz
  exact h k r ε e f wf z0 z c ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem QuotProdK_holds : Formalism.L2.SG.Pf.WFL.QuotProdK := quotient_product_compact

end Formalism.L2.SG.Closed.BM
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec.LS

open Formalism.L2.SG.Pf.WuDec

section Facts

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def Hfix (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
    (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧ uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)}

theorem NHloc_eq (v : InfinitePlace X.B.I.F) : NHloc X u v = QPK.prodSet (Nloc X u v) (Hfix X u v) := by
  unfold NHloc QPK.prodSet Hfix; rw [Hloc_eq]

theorem place_facts (v : InfinitePlace X.B.I.F) :
    IsClosed (Nloc X u v) ∧ IsCompact (Hfix X u v) ∧ QPK.IsGrp (Nloc X u v) ∧ QPK.IsGrp (Hfix X u v) ∧
    (∀ h ∈ Hfix X u v, ∀ m ∈ Nloc X u v, h * m * h⁻¹ ∈ Nloc X u v) ∧
    (∀ μ : Measure (Formalism.REAL.UJ (X.B.I.ε v)), SigmaFinite μ → μ ≠ 0 → μ (Nloc X u v)ᶜ = 0 →
      (∀ s ∈ Nloc X u v, μ.map (fun x => s * x) = μ) → ∀ s ∈ Nloc X u v, μ.map (fun x => x * s) = μ) := by
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have R := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    have := R (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b => by
    have := R (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => by
      have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) := by
    have := R (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
    rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2
  have hP := locHN_cast Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v)
    hew hfw hzw
  have hU := nUnimod_cast Formalism.L2.SG.Closed.BM.NUnimodLoc_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v)
    hew hfw hzw
  exact ⟨hP.1, hP.2.1, hP.2.2.1, ⟨fix_one, fun a ha b hb => fix_mul ha hb, fun a ha => fix_inv ha⟩,
    fun h hh m hm => hP.2.2.2 h hh m hm, hU⟩

end Facts

section K1

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem quot_rightInv {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞} (hQ : QuotWit X u μS νl C)
    (v : InfinitePlace X.B.I.F) (F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    ∫⁻ x, F (x * g) ∂(νl v) = ∫⁻ x, F x ∂(νl v) := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := place_facts X u v
  obtain ⟨-, -, hloc, -⟩ := hQ
  obtain ⟨hSv, hW⟩ := hloc v
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v)
    (Hfix X u v) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  have hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v)) := by
    rw [← NHloc_eq]; exact hSv
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM
  set β' : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x => c⁻¹ * β x with hβ'
  have hβ'm : Measurable β' := measurable_const.mul hβm
  have hβ'1 : ∀ x, ∫⁻ s, β' (s * x) ∂(μS v) = 1 := by
    intro x
    rw [hμS, lintegral_smul_measure, hβ', lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
      smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]
  have hinv' : ∀ s ∈ NHloc X u v, ∀ x, F (s * x * g) = F (x * g) := fun s hs x => by
    rw [mul_assoc]; exact hinv s hs (x * g)
  have hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x * g) = F (x * g) := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv' s (by simpa using hs) x
  have hae2 : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv s (by simpa using hs) x
  have hR := Formalism.REAL.unimodular _ (X.B.I.ε v) g
  have hmg : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g := measurable_mul_const g
  have hmgi : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g⁻¹ := measurable_mul_const g⁻¹
  calc ∫⁻ x, F (x * g) ∂(νl v)
      = ∫⁻ x, ∫⁻ s, F (s * x * g) * β' (s * x) ∂(μS v) ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => β' (s * x)) _ (hβ'm.comp (measurable_mul_const x)), hβ'1 x, mul_one]
    _ = ∫⁻ y, F (y * g) * β' y ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
        (hW (fun y => F (y * g) * β' y) ((hF.comp hmg).mul hβ'm)).symm
    _ = ∫⁻ y, F y * β' (y * g⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
        conv_rhs => rw [← hR]
        have hm2 : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => F y * β' (y * g⁻¹) := hF.mul (hβ'm.comp hmgi)
        rw [lintegral_map hm2 hmg]
        simp only [mul_inv_cancel_right]
    _ = ∫⁻ x, ∫⁻ s, F (s * x) * β' (s * x * g⁻¹) ∂(μS v) ∂(νl v) :=
        hW (fun y => F y * β' (y * g⁻¹)) (hF.mul (hβ'm.comp hmgi))
    _ = ∫⁻ x, F x ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae2 x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => β' (s * x * g⁻¹)) _ (hβ'm.comp ((measurable_mul_const x).mul_const g⁻¹))]
        simp only [mul_assoc]; rw [hβ'1 (x * g⁻¹), mul_one]

theorem quot_bruhat {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞} (hQ : QuotWit X u μS νl C)
    (v : InfinitePlace X.B.I.F) : ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) →
        ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x * β x ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := place_facts X u v
  obtain ⟨-, -, hloc, -⟩ := hQ
  obtain ⟨hSv, hW⟩ := hloc v
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v)
    (Hfix X u v) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  have hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v)) := by
    rw [← NHloc_eq]; exact hSv
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM
  refine ⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun F hF hinv => ?_⟩
  have hβ'1 : ∀ x, ∫⁻ s, c⁻¹ * β (s * x) ∂(μS v) = 1 := by
    intro x
    rw [hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
      smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]
  have hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv s (by simpa using hs) x
  calc ∫⁻ x, F x ∂(νl v)
      = ∫⁻ x, ∫⁻ s, F (s * x) * (c⁻¹ * β (s * x)) ∂(μS v) ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => c⁻¹ * β (s * x)) _
            (measurable_const.mul (hβm.comp (measurable_mul_const x))), hβ'1 x, mul_one]
    _ = ∫⁻ x, F x * (c⁻¹ * β x) ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
        (hW (fun y => F y * (c⁻¹ * β y)) (hF.mul (measurable_const.mul hβm))).symm

end K1

section Schur

open Classical

variable {D : D7} (X : HidaSetting D)

theorem pv_conv (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) :
    Integrable (fun g => Pv X v g * Pv X v (g⁻¹ * y)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
      ∫ g, Pv X v g * Pv X v (g⁻¹ * y) ∂(Formalism.REAL.muG (X.B.I.ε v)) = Pv X v y := by
  haveI : (Formalism.REAL.muG (X.B.I.ε v)).IsInvInvariant := ⟨Formalism.REAL.invInvariant _ (X.B.I.ε v)⟩
  have hds := X.ds v
  have hU := hds.2.2.1
  have hURep : Formalism.L2.SG.ProjRows.IsURep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g)) := by
    refine ⟨?_, fun a b => ?_, fun g w => hU.2.1 _ g.2 w, fun w => ?_⟩
    · show X.B.σ v (uMat 1) = 1
      rw [uMat_one']; exact hU.1.1
    · show X.B.σ v (uMat (a * b)) = (X.B.σ v (uMat a)).comp (X.B.σ v (uMat b))
      rw [Formalism.L2.SG.WuDecayPf.uMat_mul']; exact hU.1.2 _ a.2 _ b.2
    · exact (hU.2.2 w).comp_continuous Formalism.L2.SG.WuDecayPf.continuous_uMat (fun g => g.2)
  haveI : Nontrivial (X.B.H v) := hds.2.1
  obtain ⟨d', hd'⟩ := PIW.HCFdeg.formal_degree_abstract_form _ (X.B.I.ε v) (X.B.H v) (X.B.σ v) hds.2.2.1 hds.2.2.2.1 hds.2.2.2.2.1
  have hw1 : ‖X.B.w v‖ = 1 := (X.low v).1
  have hw0 : X.B.w v ≠ 0 := by intro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  have hdd : X.dv v = d' := Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd' hw0
  have hF : Formalism.L2.SG.ProjRows.IsFdegG (Formalism.REAL.muG (X.B.I.ε v)) (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g))
      (X.dv v) := by
    rw [hdd]; exact ⟨hd'.1, fun a b a' b' => hd'.2 a b a' b'⟩
  obtain ⟨hPC, -⟩ := Formalism.L2.SG.Closed.SchurConv_holds (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (X.B.H v)
    (fun g => X.B.σ v (uMat g)) (X.dv v) (X.B.w v) hURep hF hw1
  obtain ⟨h1, -, h3⟩ := hPC
  obtain ⟨hi, he⟩ := h3 1 y
  simp only [inv_one, one_mul] at hi he
  rw [h1, one_mul] at he
  exact ⟨hi, he⟩

end Schur

section Main

open Classical Formalism.L2.SG.SplitPrimeNormLemmas

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem pv_integrable (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (v : InfinitePlace X.B.I.F) :
    Integrable (Pv X v) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X (coefWeighted_of_gap X Formalism.L2.SG.Closed.BM.CoefWeightedLoc_holds hG) v
  have e : Pv X v = fun g => ((X.dv v : ℝ) : ℂ) * star (Formalism.L2.SG.WuDecayPf.coefV X v g) := by
    funext g; rfl
  refine Integrable.mono' (h.norm.const_mul |X.dv v|) (continuous_Pv X v).aestronglyMeasurable
    (ae_of_all _ fun g => le_of_eq ?_)
  rw [e]
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]

theorem ennreal_mul_le_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem local_scalar_reduction : LocScalarStep := by
  intro D hG X u μS νl C hQ v c hc0 hc
  set μ := Formalism.REAL.muG (X.B.I.ε v) with hμ
  set f := X.Wloc u v with hfdef
  set ph := Pv X v with hph
  have hfc : Continuous f := X.Wloc_cont u v
  have hpc : Continuous ph := continuous_Pv X v
  have hpI : Integrable ph μ := pv_integrable X hG v
  obtain ⟨hL0, hLt⟩ := localRepresentationL2 X u hQ v
  obtain ⟨β, hβm, hβ⟩ := quot_bruhat X u hQ v
  set ν' := μ.withDensity β with hν'
  have htr : ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) →
      ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x ∂ν' := by
    intro F hF hi
    rw [hβ F hF hi, hν', lintegral_withDensity_eq_lintegral_mul _ hβm hF]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]; ring
  set L := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(νl v) with hL
  have hinvN : ∀ s ∈ NHloc X u v, ∀ x, ‖f (s * x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
    intro s hs x
    obtain ⟨m, hm, h, hh, rfl⟩ := hs
    have hs' : m * h ∈ Sloc X u v := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    rw [← enorm_norm (f (m * h * x)), norm_Wloc_inv X u v hs', enorm_norm]
  have hK1 : ∀ y, ∫⁻ x, ‖f (x * y)‖ₑ ^ 2 ∂ν' = L := fun y => by
    rw [← htr (fun x => ‖f (x * y)‖ₑ ^ 2) ((hfc.comp (continuous_id.mul continuous_const)).enorm.measurable.pow_const 2)
      (fun s hs x => by simp only [mul_assoc]; exact hinvN s hs (x * y))]
    exact quot_rightInv X u hQ v (fun x => ‖f x‖ₑ ^ 2) (hfc.enorm.measurable.pow_const 2) hinvN y
  have hL' : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν' = L := (htr _ (hfc.enorm.measurable.pow_const 2) hinvN).symm
  have hin : ∀ y, ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ 2 * L := by
    intro y
    calc ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ ∫⁻ x, (‖f x‖ₑ ^ 2 + ‖f (x * y)‖ₑ ^ 2) ∂ν' :=
          lintegral_mono fun x => ennreal_mul_le_sq _ _
      _ = L + L := by
          rw [lintegral_add_left (hfc.enorm.measurable.pow_const 2), hK1 y, hL']
      _ = 2 * L := (two_mul L).symm
  have mf : Measurable fun y => ‖f y‖ₑ := hfc.enorm.measurable
  have mp : Measurable fun y => ‖ph y‖ₑ := hpc.enorm.measurable
  set A : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x =>
    ∫⁻ g, ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ ∂μ with hA

  set T : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ :=
    fun x g h => ‖f x‖ₑ * (‖ph g‖ₑ * (‖ph h‖ₑ * ‖f (x * g * h)‖ₑ)) with hTdef
  have hTm : Measurable fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
      T p.1.1 p.1.2 p.2 := by
    have h3 : Continuous fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
        f (p.1.1 * p.1.2 * p.2) :=
      hfc.comp (((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul continuous_snd)
    exact (mf.comp (measurable_fst.comp measurable_fst)).mul ((mp.comp (measurable_snd.comp measurable_fst)).mul
      ((mp.comp measurable_snd).mul h3.enorm.measurable))
  have hTm' : ∀ g, Measurable fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => T p.1 g p.2 := by
    intro g
    exact hTm.comp (measurable_fst.prodMk measurable_const |>.prodMk measurable_snd)
  have e1 : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' = ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ := by
    have step1 : ∀ x, ‖f x‖ₑ * A x = ∫⁻ g, ∫⁻ h, T x g h ∂μ ∂μ := by
      intro x
      rw [hA]
      simp only []
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun g => ?_
      rw [← lintegral_const_mul' _ _ enorm_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]
    simp only [step1]
    rw [lintegral_lintegral_swap (hTm.lintegral_prod_right').aemeasurable]
    refine lintegral_congr fun g => ?_
    exact lintegral_lintegral_swap (hTm' g).aemeasurable
  have hT : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' < ⊤ := by
    rw [e1]
    have hb : ∀ g h, ∫⁻ x, T x g h ∂ν' ≤ ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) := by
      intro g h
      have : ∀ x, T x g h = ‖ph g‖ₑ * (‖ph h‖ₑ * (‖f x‖ₑ * ‖f (x * (g * h))‖ₑ)) := by
        intro x; simp only [hTdef, mul_assoc]; ring
      simp only [this]
      rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_const_mul' _ _ enorm_ne_top]
      gcongr
      exact hin _
    calc ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ ≤ ∫⁻ g, ∫⁻ h, ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) ∂μ ∂μ :=
          lintegral_mono fun g => lintegral_mono fun h => hb g h
      _ = (∫⁻ g, ‖ph g‖ₑ ∂μ) * ((∫⁻ h, ‖ph h‖ₑ ∂μ) * (2 * L)) := by
          rw [← lintegral_mul_const _ mp]
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_mul_const _ mp]
      _ < ⊤ := ENNReal.mul_lt_top hpI.2 (ENNReal.mul_lt_top hpI.2
          (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.2 hLt)))

  obtain ⟨x, hfx, hAx⟩ : ∃ x, f x ≠ 0 ∧ A x < ⊤ := by
    by_contra hcon
    push Not at hcon
    set E := {x | f x ≠ 0} with hE
    have hEm : MeasurableSet E := (isClosed_eq hfc continuous_const).isOpen_compl.measurableSet
    have hE0 : ν' E ≠ 0 := by
      intro h0
      apply hL0
      rw [← hL']
      apply (lintegral_eq_zero_iff (mf.pow_const 2)).2
      have : ∀ᵐ y ∂ν', y ∉ E := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with y hy
      simp only [hE, Set.mem_setOf_eq, not_not] at hy
      simp [hy]
    have hle : ∀ y, E.indicator (fun _ => (⊤ : ℝ≥0∞)) y ≤ ‖f y‖ₑ * A y := by
      intro y
      by_cases hy : y ∈ E
      · rw [Set.indicator_of_mem hy, top_le_iff, top_le_iff.1 (hcon y hy), ENNReal.mul_top]
        exact enorm_ne_zero.2 hy
      · rw [Set.indicator_of_notMem hy]; exact zero_le
    have := lt_of_le_of_lt (lintegral_mono hle) hT
    rw [lintegral_indicator_const hEm, ENNReal.top_mul hE0] at this
    exact lt_irrefl _ this

  set Φ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph p.2 • f (x * p.1 * p.2)) with hΦ
  have hΦc : Continuous Φ :=
    (hpc.comp continuous_fst).smul ((hpc.comp continuous_snd).smul
      (hfc.comp ((continuous_const.mul continuous_fst).mul continuous_snd)))
  have hΦi : Integrable Φ (μ.prod μ) := by
    refine ⟨hΦc.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Φ p‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod _ hΦc.enorm.aemeasurable]
    have e2 : ∀ g, ∫⁻ h, ‖Φ (g, h)‖ₑ ∂μ = ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ := fun g => by
      simp only [hΦ, enorm_smul]
      rw [lintegral_const_mul' _ _ enorm_ne_top]
    simp only [e2]
    exact hAx
  have hΦv : ∫ p, Φ p ∂(μ.prod μ) = c • c • f x := by
    rw [integral_prod _ hΦi]
    have e3 : ∀ g, ∫ h, Φ (g, h) ∂μ = c • (ph g • f (x * g)) := fun g => by
      simp only [hΦ]
      rw [integral_smul, (hc (x * g)).2, smul_comm]
    simp only [e3]
    rw [integral_smul, (hc x).2]
  have hS := measurePreserving_prod_mul μ μ
  have he : MeasurableEmbedding (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) :=
    (MeasurableEquiv.shearMulRight (Formalism.REAL.UJ (X.B.I.ε v))).measurableEmbedding
  set Ψ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph (p.1⁻¹ * p.2) • f (x * p.2)) with hΨ
  have hcomp : Ψ ∘ (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) = Φ := by
    funext z
    simp only [Function.comp_apply, hΨ, hΦ, inv_mul_cancel_left, mul_assoc]
  have hΨi : Integrable Ψ (μ.prod μ) := (hS.integrable_comp_emb he).1 (by rw [hcomp]; exact hΦi)
  have hΨv : ∫ p, Ψ p ∂(μ.prod μ) = c • f x := by
    rw [integral_prod_symm _ hΨi]
    have e4 : ∀ y, ∫ g, Ψ (g, y) ∂μ = ph y • f (x * y) := fun y => by
      simp only [hΨ, smul_smul]
      rw [integral_smul_const, (pv_conv X v y).2]
    simp only [e4]
    exact (hc x).2
  have hΦΨ : ∫ p, Φ p ∂(μ.prod μ) = ∫ p, Ψ p ∂(μ.prod μ) := by
    rw [← hcomp]
    exact hS.integral_comp he Ψ
  rw [hΦv, hΨv, smul_smul] at hΦΨ
  have h5 : (c * c - c) • f x = 0 := by rw [sub_smul, hΦΨ, sub_self]
  have h6 : c * c - c = 0 := (smul_eq_zero.1 h5).resolve_right hfx
  have h7 : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact h6
  exact sub_eq_zero.1 ((mul_eq_zero.1 h7).resolve_left hc0)

end Main

end Formalism.L2.SG.Pf.WuDec.LS
end
end

section
namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Closed.BM

theorem wuDecayOfGap_of_uniqGap (h : CompanionTheory.Lime.BM.UniqGap) : WuDecayOfGap :=
  WuDec.BM.wuDecay_gap h BesselNVGap_holds CoefWeightedLoc_holds WlocExists_holds QuotProdK_holds NUnimodLoc_holds
    WuDec.LS.local_scalar_reduction

end Formalism.L2.SG.Pf
end

section
noncomputable section

namespace CompanionTheory.Lime.BM

open Formalism.L2.SG.BesselSplit

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory Finset
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselSplitLargeGap : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    1 ≤ k → Formalism.QuantumDeterminants.GapAtLeast ε lam h → 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∃ B : H → Vp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
    ∃ v ∈ smoothVecs (k := k) (r := r) σ, ∃ v' ∈ smoothVecs (k := k) (r := r) σ,
      beOp μW μN σ π (psiGen k r z c) v v' ≠ 0

end CompanionTheory.Lime.BM
end
end

section
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature Formalism.L2.SG.BesselSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace BM

theorem besselSchur'_of_dec (hJ : CompanionTheory.Lime.BM.UniqGap) (hI : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) (hAt : CompanionTheory.Lime.BM.AtFormAdmOne)
    (hBP : CompanionTheory.Lime.BM.BesselSplitLargeGap) (hSI : Formalism.L2.SG.BesselSplit.SmoothIrred)
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hT : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ParamTieG D Cn) :
    Formalism.MainNotions.S.Pv.Mom.BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hTw v hv
  obtain ⟨hka, hG0⟩ := hT hH
  obtain ⟨h, hgap, hok⟩ := hG0 τ lam' hl hA.1
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hTw
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, -, hcN, hl2, -, -⟩ := hA'

  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hN, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]; exact Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκtop

  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hc1ne : c1 ≠ 0 := by
    have e : (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) = 2 * kaS D := by
      unfold kaS gg; ring
    rw [hc1def, e]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hDSH

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDSd⟩ := hDSH2
  obtain ⟨S, hS⟩ := hDSd.2.2.2.2.2.1
  obtain ⟨v1, hv1S, hv10, -⟩ := hS.2.2.2.1
  set w0 : A.H := ((‖v1‖⁻¹ : ℝ) : ℂ) • v1 with hw0def
  have hw0 : IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := by
    refine ⟨PD, hPD, ?_, ?_⟩
    · rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv10)
    · exact (le_sSup (show S ∈ {S | IsKTypeOf (epsSH D.R) _ (lowK (epsSH D.R) lam') S} from hS)) (S.smul_mem _ hv1S)
  have hw0sm : IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ w0 :=
    hI.2.2.1 _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH w0
      ⟨S, hS.1, S.smul_mem _ hv1S, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hPD hS.2.1⟩
  have hsmx : ∀ x ∈ UH (Hpk D.R.k D.R.rS), IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ (A.σ x w0) :=
    fun x hx => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw0sm hx

  have hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam' h A.σ w0 W.z c1 (fun i => ((D.hcW w τ).u i : ℝ))
      W.π W.μW W.μN W.μG W.νS :=
    ⟨hHC, hDSH, hgap, hok, hw0, hz, hTpos, hc1ne, hc1, hUW, hNH, hG, hq⟩
  obtain ⟨l, hlB, hla, hlb⟩ := hAt hI _ _ _ _ h A.H A.σ w0 W.Wp W.z c1 _ W.π W.μW W.μN W.μG W.νS hSide

  have hS'0 := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  have hae0 : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS'0 hq

  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hBnz : ∃ x ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ, A.B x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hz0 : l2SG W.νS A.Φ = 0 := by
      unfold l2SG
      refine (lintegral_congr_ae ?_).trans (lintegral_zero)
      filter_upwards [hae0] with y hy
      show (‖A.B (A.σ (Matrix.of y) A.v0)‖₊ : ℝ≥0∞) ^ 2 = 0
      rw [hc _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0s hy)]
      simp
    rw [hl2] at hz0
    have hm0 : 0 < A.cN * (Module.finrank ℂ W.Wp : ℝ) := mul_pos hcN (by exact_mod_cast Module.finrank_pos)
    exact (ENNReal.ofReal_pos.2 hm0).ne' hz0
  obtain ⟨v1', hv1', v2', hv2', hne0⟩ := hBP _ _ (epsSH D.R) lam' h A.H A.σ W.z (fun _ => c1) _ W.Wp W.π W.μW W.μN
    hok.1 hgap hok.2.1 hHC hDSH hz hTpos (fun _ => hc1ne) hc1 hUW hNH ⟨A.B, by rw [psiGen_const]; exact hB1, hBnz⟩
  have hw0ne : w0 ≠ 0 := by
    intro h0; obtain ⟨-, -, hn, -⟩ := hw0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨mm, hmA, hmm⟩ := Formalism.L2.S.Pv.PeriodG.exponent_ok _ _ hok (epsSH D.R)
  obtain ⟨hI', hC1, hC2⟩ := Formalism.L2.S.Pv.PeriodG.periodContG_at (fun _ => c1) mm hHC hDSH hz hTpos hc1 hUW hNH hG hq
    hgap hmm hmA
  obtain ⟨x, hx, x₀, hx₀, hne⟩ := trans' hSI hHC hDSH hw0sm hw0ne hsmx hv1' hv2' hI' hC1 hC2 hne0
  unfold Formalism.L2.SG.BesselSplit.beOp Formalism.L2.SG.BesselSplit.beInt at hne
  rw [psiGen_const] at hne
  have hadm : Formalism.FourierDecayAlt.ThreeDimData.IsAdm A.σ w0 (A.σ x₀ w0) := Or.inl (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
  obtain ⟨-, heq⟩ := hla (A.σ x w0) (hsmx x hx) (A.σ x₀ w0) hadm
  have hlv : l (A.σ x₀ w0) ≠ 0 := by
    intro h0
    apply hne
    rw [heq, h0]
    ext y
    simp

  obtain ⟨d, hd, hSch⟩ := Formalism.MainNotions.DiscreteSeriesInnerProducts.schurH A.σ hDSH hG
  have hfd : ∀ u : A.H, u ≠ 0 → fdegH W.μG A.σ u = d :=
    fun u hu => Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegH_eq hd (fun v w v' w' => (hSch v w v' w').2) hu
  have hl0 : l 0 = 0 := by
    have := hlB.2.1 0 0 (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero)
    simpa using this
  have hlp : 0 < ‖l (A.σ x₀ w0)‖ ^ 2 := by positivity
  have hl2l : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => l (A.σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      unfold l2SG
      simp [hl0]
    · have e := hlb u hu hu0 _ hadm
      have e2 : ENNReal.ofReal (‖u‖ ^ 2 * ‖l (A.σ x₀ w0)‖ ^ 2 / fdegH W.μG A.σ u) =
          ENNReal.ofReal (‖l (A.σ x₀ w0)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
        rw [hfd u hu0, ← ENNReal.ofReal_mul hlp.le]
        congr 1
        ring
      erw [e2] at e
      exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hlp).ne' ENNReal.ofReal_ne_top).1 e

  obtain ⟨α, β, hαβ, hrel⟩ := hJ _ _ (epsSH D.R) lam' h A.H A.σ W.z (fun _ => c1) _ W.Wp W.π hok.1 hgap hok.2.1 hHC hDSH hz hTpos
    (fun _ => hc1ne) hc1 A.B l (by rw [psiGenPI_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mp hB1)
    (by rw [psiGenPI_const]; exact hlB)
  have hα : α ≠ 0 := by
    intro h0
    rcases hαβ with h1 | h1
    · exact h1 h0
    · have e := hrel _ (hsmx x₀ hx₀)
      rw [h0, zero_smul, zero_add] at e
      exact hlv ((smul_eq_zero.1 e).resolve_left h1)
  have hBl : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → A.B u = (-(β / α)) • l u := by
    intro u hu
    have e := hrel u hu
    have e2 : α • A.B u = -(β • l u) := eq_neg_of_add_eq_zero_left e
    calc A.B u = α⁻¹ • (α • A.B u) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
      _ = α⁻¹ • (-(β • l u)) := by rw [e2]
      _ = (-(β / α)) • l u := by rw [smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]

  have hS' := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  have hae : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS' hq
  have hl2B : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => A.B (A.σ g u)) = ENNReal.ofReal (‖-(β / α)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    rw [← hl2l u hu]
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hBl _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hu hy), nnnorm_smul, ENNReal.coe_mul, mul_pow,
      Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have hΦ : l2SG W.νS A.Φ = l2SG W.νS (fun g => A.B (A.σ g A.v0)) := rfl
  rw [hΦ, hl2B v hv, hl2B A.v0 hv0s, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq A.v0, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq v,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem moment_bound_schur (hJ : CompanionTheory.Lime.BM.UniqGap) (hBP : CompanionTheory.Lime.BM.BesselSplitLargeGap)
    (hSI : Formalism.L2.SG.BesselSplit.SmoothIrred) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) :
    Formalism.MainNotions.S.Pv.Mom.MomF' Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.S.Pv.Mom.momF'_of_schur_at Fm Cg cb Cu cT CT C0
    (fun Cn => Formalism.MainNotions.S.OwnEv.mono
      (fun C' Cl x i h => besselSchur'_of_dec hJ CompanionTheory.Lime.BM.inputs
        (CompanionTheory.Lime.BM.atFormAdmOne hJ) hBP hSI _ _ _ _ _ _ _ _ _ _ Cn h)
      (parameter_gap_family Fm Cg cb Cu cT CT C0 Cn))
    (fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => lowKOneAt_of_tieG _ _ _ _ _ _ _ _ _ _ Cn h)
      (parameter_gap_family Fm Cg cb Cu cT CT C0 Cn))
    Formalism.L2.SG.Pf.k_finite_smooth_bessel


end BM

end Formalism.L2.S.Pv.Mom
end
end

section
namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants


end CompanionTheory.Lime.BM
end

section
namespace CompanionTheory.Lime.BM


theorem wuDecayOfGap (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  Formalism.L2.SG.Pf.wuDecayOfGap_of_uniqGap h


theorem ampUnif (h : CompanionTheory.Bmu.BesselMapUniqGap) : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif :=
  Formalism.L2.S.Pv.AmpOrbCoef.BM.ampUnif_gap h
    fun k r ε lam H _ _ _ σ hl hσ v hv Ws hWs e he => Formalism.MainStatements.RankOne.KD.kDense k r ε lam H σ hl hσ v hv Ws hWs e he

end CompanionTheory.Lime.BM
end

section
namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions

theorem uniqGap_holds : UniqGap := CompanionTheory.Bmu.besselMapUniqGap

theorem ampUnif_holds : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif := ampUnif CompanionTheory.Bmu.besselMapUniqGap

theorem wuDecayOfGap_holds' : Formalism.L2.SG.Pf.WuDecayOfGap := wuDecayOfGap CompanionTheory.Bmu.besselMapUniqGap

end CompanionTheory.Lime.BM
end
