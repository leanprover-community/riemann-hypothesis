import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZTie
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ} {κ τ : ℝ}

theorem phiP_stabAct (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    phiP k r κ τ (stabAct g a x) = stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) := by
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · show (fun i j => cj k r κ τ (a * Matrix.of x2) i j) =
      fun i j => (cj k r κ τ a * Matrix.of (cjT k r κ τ x2)) i j
    rw [cj_mul hκ hτ]
    rfl
  · show (fun i j => cj k r κ τ (g⁻¹ * a * g * Matrix.of x4) i j) =
      fun i j => ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * Matrix.of (cjT k r κ τ x4)) i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
    rfl

theorem isOrbQuot_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (h : IsOrbQuot L g μR ν) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
      (μR.map (cjT k r κ τ)) (ν.map (phiP k r κ τ)) := by
  intro f hf
  rw [pairMeas_trD hκ hτ]
  have exp_product_square_inv : (pairMeas L).map (phiP k r κ τ) = (pairMeas L).map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [exp_product_square_inv, lintegral_map_equiv]
  rw [h (fun x => f (phiE hκ hτ x)) (hf.comp (phiE hκ hτ).measurable)]
  have eP : ν.map (phiP k r κ τ) = ν.map (phiE (k := k) (r := r) hκ hτ) := rfl
  rw [eP, lintegral_map_equiv]
  refine lintegral_congr (fun x => ?_)
  have eT : μR.map (cjT k r κ τ) = μR.map (cjE (k := k) (r := r) hκ hτ) := rfl
  rw [eT, lintegral_map_equiv]
  refine lintegral_congr (fun a => ?_)
  show f (phiP k r κ τ (stabAct g (Matrix.of a) x)) =
    f (stabAct (cj k r κ τ g) (Matrix.of (cjT k r κ τ a)) (phiP k r κ τ x))
  rw [phiP_stabAct hκ hτ]
  rfl

theorem isRelStab_trD (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {g : Mx k r} (h : IsRelStab L g) :
    IsRelStab (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') (cj k r κ τ g) := by
  intro a ha
  obtain ⟨b, rfl⟩ : ∃ b, a = cj k r κ τ b := ⟨cjI k r κ τ a, (cj_cjI hκ hτ a).symm⟩
  have hb : b ∈ RStab k r g := (cj_mem_RStab_iff hκ hτ g b).1 ha
  have e : (cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g = cj k r κ τ (g⁻¹ * b * g) := by
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]
  show psi k r ((τ : ℂ) • L.z) ((κ : ℂ) * L.c) (cj k r κ τ b) =
    psi k r ((τ : ℂ) • L.z') ((κ : ℂ) * L.c) ((cj k r κ τ g)⁻¹ * cj k r κ τ b * cj k r κ τ g)
  rw [e, psi_cj hκ hτ L.hz.1, psi_cj hκ hτ L.hz'.1]
  exact h b hb

theorem isOrbQuot_smul {L L' : LocBessel k r} {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (h : IsOrbQuot L g μR ν) (t : ENNReal) (hP : pairMeas L' = t • pairMeas L) : IsOrbQuot L' g μR (t • ν) := by
  intro f hf
  rw [hP, lintegral_smul_measure, lintegral_smul_measure, h f hf]

theorem pairMeas_scaleN {L L' : LocBessel k r} (hW : L'.μW = L.μW) (hW' : L'.μW' = L.μW') (t : ENNReal)
    (hN : L'.μN = t • L.μN) : pairMeas L' = (t * t) • pairMeas L := by
  haveI : SFinite L.μN := sFinite_haarLie _ _
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  unfold pairMeas
  rw [hW, hW', hN, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, smul_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

abbrev standardBesselDatumRescaled (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (κ₀ : ENNReal) : LocBessel k r :=
  { stdL L ka hka with κN := κ₀ }

def gStd (ka : ℝ) (g : Mx k r) : Mx k r := cj k r ka⁻¹ 1 (tTi k r * g * tT k r)

def muStd (ka : ℝ) (μR : Measure (Mt k r)) : Measure (Mt k r) := (μR.map (cA k r)).map (cjT k r ka⁻¹ 1)

theorem haarLie_smul (S : Set (Mx k r)) (a b : ENNReal) : haarLie S (a * b) = a • haarLie S b := by
  show (a * b) • _ = a • (b • _)
  rw [smul_smul]

theorem orbJ_std (hk : 1 ≤ k) (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (hN0 : L.κN ≠ 0) (hN1 : L.κN ≠ ⊤) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤)
    (B : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq) (hBz : B.z = (stdL L ka hka).z) (hBz' : B.z' = (stdL L ka hka).z')
    (hBπ : B.π = (stdL L ka hka).π) (hBπ' : B.π' = (stdL L ka hka).π') (hBW : B.μW = (stdL L ka hka).μW)
    (hBW' : B.μW' = (stdL L ka hka).μW') (hBN : B.μN = haarLie (Nset k r) κ₀)
    (g : Mx k r) (hg : g ∈ UH (Hpk k r)) (hrel : IsRelStab L g) (μR : Measure (Mt k r)) [SFinite μR]
    (hconc : μR {x | Matrix.of x ∉ RStab k r g} = 0) (hne : μR ≠ 0) (ν : Measure (PairSp k r))
    (hq : IsOrbQuot L g μR ν) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (hcut : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS) :
    Formalism.FourierDecayAlt.D.orbJ B (gStd ka g) (muStd ka μR) (stdF L ka F) =
      (((κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1))) * (κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1)))).toReal
        : ℂ) • OrbInt L F g ν := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hκ : (0 : ℝ) < ka⁻¹ := inv_pos.2 hka
  have hτ : (0 : ℝ) < 1 := one_pos
  set κs : ENNReal := L.κN * ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) with hκs
  have hd : ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) ≠ 0 := (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  have hs0 : κs ≠ 0 := mul_ne_zero hN0 hd
  have hs1 : κs ≠ ⊤ := ENNReal.mul_ne_top hN1 ENNReal.ofReal_ne_top
  set t : ENNReal := κ₀ / κs with ht
  set g1 := tTi (k0 + 1) r * g * tT (k0 + 1) r with hg1

  have hq1 : IsOrbQuot (turnL L ka) g1 (μR.map (cA (k0 + 1) r)) (ν.map (thP (k0 + 1) r)) := isOrbQuot_turn L ka hq
  have hrel1 : IsRelStab (turnL L ka) g1 := isRelStab_turn L ka hc hrel

  have hqs : IsOrbQuot (stdL L ka hka) (gStd ka g) (muStd ka μR) ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1)) :=
    isOrbQuot_trD hκ hτ (turnL L ka) _ _ _ _ _ _ hq1
  have hrels : IsRelStab (stdL L ka hka) (gStd ka g) := isRelStab_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ hrel1

  have hNs : (standardBesselDatumRescaled L ka hka κ₀).μN = t • (stdL L ka hka).μN := by
    show haarLie (Nset (k0 + 1) r) κ₀ = t • haarLie (Nset (k0 + 1) r) κs
    rw [← haarLie_smul, ht, ENNReal.div_mul_cancel hs0 hs1]
  have hP2 : pairMeas (standardBesselDatumRescaled L ka hka κ₀) = (t * t) • pairMeas (stdL L ka hka) :=
    pairMeas_scaleN (L := stdL L ka hka) (L' := standardBesselDatumRescaled L ka hka κ₀) rfl rfl t hNs
  have hq2 : IsOrbQuot (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) (muStd ka μR)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) := isOrbQuot_smul hqs _ hP2
  have hrel2 : IsRelStab (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) := hrels
  have hc2 : (standardBesselDatumRescaled L ka hka κ₀).c = cStd := stdL_c L ka hka

  have hg2 : gStd ka g ∈ UH (Hpk (k0 + 1) r) := (cj_mem_UH_iff hκ hτ _).mpr (conjI_mem_UH hg)
  have hmem : ∀ x : Mt (k0 + 1) r, (Matrix.of (cjT (k0 + 1) r ka⁻¹ 1 (cA (k0 + 1) r x)) ∈ RStab (k0 + 1) r (gStd ka g)) ↔
      Matrix.of x ∈ RStab (k0 + 1) r g := by
    intro x
    rw [of_cjT, of_cA]
    exact (cj_mem_RStab_iff hκ hτ _ _).trans (conjI_mem_RStab_iff g _)
  have hconc2 : muStd ka μR {x | Matrix.of x ∉ RStab (k0 + 1) r (gStd ka g)} = 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, MeasurableEquiv.map_apply, ← cAE_coe, MeasurableEquiv.map_apply]
    convert hconc using 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, cAE_coe, cjE_coe]
    exact not_congr (hmem x)
  have hne2 : muStd ka μR ≠ 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, ← cAE_coe]
    exact (Measure.map_ne_zero_iff (cjE hκ hτ).measurable.aemeasurable).mpr
      ((Measure.map_ne_zero_iff (cAE (k0 + 1) r).measurable.aemeasurable).mpr hne)
  have : SFinite (muStd ka μR) := by unfold muStd; infer_instance

  obtain ⟨θ, hθ, hint⟩ := hcut
  have hμ : B.μSS = pairMeas (standardBesselDatumRescaled L ka hka κ₀) := by
    show (B.μW.prod B.μN).prod (B.μW'.prod B.μN) = _
    rw [hBW, hBN, hBW']
    rfl
  have hI : ∀ θ' : Formalism.FourierDecayAlt.B.SS (k0 + 1) r → ℝ,
      (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) =
      fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p := by
    intro θ'
    funext p
    exact congrArg (fun X => θ' p • X)
      (Formalism.MainNotions.BigCellDensity.integrand_eq (standardBesselDatumRescaled L ka hka κ₀) B hc2 hBz hBz' hBπ hBπ' (stdF L ka F) (gStd ka g) p)
  have hW := Formalism.MainNotions.BigCellDensity.weil_L_gen (standardBesselDatumRescaled L ka hka κ₀) hc2 h0 h1 hg2 hrel2 hconc2 hne2 hq2 (stdF L ka F)
  have hfin : OrbInt (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = ((t * t).toReal : ℂ) • OrbInt L F g ν := by
    show OrbInt (stdL L ka hka) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = _
    rw [gStd, OrbInt_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ (stdF L ka F) g1 (t * t) (ν.map (thP (k0 + 1) r))]
    have hfe : (fun x => stdF L ka F (cj (k0 + 1) r ka⁻¹ 1 x)) = turnF L ka F := by
      funext x
      show turnF L ka F (cjI (k0 + 1) r ka⁻¹ 1 (cj (k0 + 1) r ka⁻¹ 1 x)) = _
      rw [cjI_cj hκ hτ]
    rw [hfe, OrbInt_turn L ka hc F g ν]
  unfold Formalism.FourierDecayAlt.D.orbJ
  rw [dif_pos ⟨θ, hθ, hint⟩]
  have hspec := (⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose_spec
  generalize (⟨θ, hθ, hint⟩ : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS).choose = θ' at hspec ⊢
  have hint' : Integrable (fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p)
      (pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    have h2 := hspec.2
    rw [hI θ', hμ] at h2
    exact h2
  have hθ1 : ∀ p, Formalism.MainNotions.BigCellDensity.InPair (standardBesselDatumRescaled L ka hka κ₀) p →
      ∫ x, θ' (stabAct (gStd ka g) (Matrix.of x) p) ∂(muStd ka μR) = 1 := by
    intro p hp
    refine hspec.1.2.2 p ?_
    unfold Formalism.FourierDecayAlt.B.RealPlaceData.inSS
    rw [hBz, hBz']
    exact hp
  have e1 : (∫ p, θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p ∂B.μSS) =
      ∫ p, θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    rw [hμ]
    exact congrArg (fun f => ∫ p, f p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀))) (hI θ')
  exact e1.trans ((hW θ' hθ1 hint').trans hfin)

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem torS_eq (δ : ℝ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ)) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r δ 1) := by
  unfold Formalism.L2.SG.LocWSOf.torS tT dM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hI0)]
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_neg]
      push_cast
      rw [mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ hI0)]

theorem torS_inv_eq (δ : ℝ) (hδ : 0 < δ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ))⁻¹ k r = (Complex.I ^ r) • (dMi k r δ 1 * tTi k r) := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold Formalism.L2.SG.LocWSOf.torS tTi dMi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_pow, one_pow]
    field_simp
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_inv₀, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
        neg_neg, inv_inv]
      rw [← Complex.inv_I]
      push_cast
      rw [inv_pow]
      field_simp
      rw [div_pow, one_pow, mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
      field_simp
      rw [div_pow, one_pow]
      field_simp

theorem nLeft_holds : Formalism.MainNotions.MeasFS.NLeft := fun k r κ h0 h1 a ha =>
  (Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1).2.2.2 a ha

theorem muN_eq_haarLie (k r : ℕ) :
    ∃ κ₀ : ENNReal, κ₀ ≠ 0 ∧ κ₀ ≠ ⊤ ∧ Formalism.FourierDecayAlt.D.muN k r = haarLie (Nset k r) κ₀ := by
  have hH := Formalism.MainNotions.MeasFS.haar_lie_measure_on_nilpotent (k := k) (r := r) nLeft_holds 1 one_ne_zero ENNReal.one_ne_top
  have hM := Formalism.FourierDecayAlt.Final.d_muNHaar k r
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) _ _ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hH
    hM.conc hM.left hM.finite_compact
  refine ⟨(c : ENNReal), fun h => hM.ne_zero ?_, ENNReal.coe_ne_top, ?_⟩
  · rw [hc, ENNReal.coe_eq_zero.mp h, zero_smul]
  · rw [hc, show ((c : ENNReal)) = (c : ENNReal) * 1 from (mul_one _).symm, haarLie_smul, ENNReal.smul_def]

def kaB (D : Formalism.BasicNotions.D7) : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

theorem kaB_pos (D : Formalism.BasicNotions.D7) : 0 < kaB D := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact div_pos hka (mul_pos hg0 hg1)

theorem muT_eq (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.LocWSOf.muT D = -Complex.I * (((kaB D)⁻¹ : ℝ) : ℂ) := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hkac : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  unfold Formalism.L2.SG.LocWSOf.muT Formalism.L2.SG.LocWSOf.cfS Formalism.L2.SG.LocWSOf.frS kaB
  push_cast
  field_simp

theorem torS_muT (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r (kaB D)⁻¹ 1) := by
  rw [muT_eq, torS_eq]

theorem torS_muT_inv (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r = (Complex.I ^ r) • (dMi k r (kaB D)⁻¹ 1 * tTi k r) := by
  rw [muT_eq, torS_inv_eq _ (inv_pos.mpr (kaB_pos D))]

theorem torS_conj (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r =
      gStd (kaB D) M := by
  rw [torS_muT, torS_muT_inv, gStd]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cj, Matrix.mul_assoc]

theorem torS_conjI (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r =
      tT k r * cjI k r (kaB D)⁻¹ 1 M * tTi k r := by
  rw [torS_muT, torS_muT_inv]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cjI, Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

theorem ampVec_gen (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne) (hAKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF)
    (hCC : Formalism.MainNotions.S.Pv.AmpDD.CellConv) {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 Cn : ℝ}
    (hGap : Formalism.MainNotions.S.Pv.AmpDD.GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w')
    (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (a b : A.H) (ξ : W.Wp) (ξ' : W.Wq)
    (hka : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ a)
    (hkb : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ b)
    (hn : ⟪A.B a, ξ⟫_ℂ * ⟪ξ', A.B' b⟫_ℂ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
      OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT')
        (Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') a b ξ ξ') γ ν = κ • A.J νR γ := by
  obtain ⟨h, hg, hok, hcell⟩ := hGap hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hJ : PI.BesselMapUniq.BesselMapUniq := hI.2.2.2
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp
  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  have has : a ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 a hka
  have hbs : b ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 b hkb
  have hBa : A.B a = c0 • l a := hc0 a has
  have hBb : A.B' b = c0' • l' b := hc0' b hbs
  rw [hBa, hBb, inner_smul_left, inner_smul_right] at hn
  have hc0ne : c0 ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  have hc0ne' : c0' ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  set s : ℂ := ⟪l a, ξ⟫_ℂ * ⟪ξ', l' b⟫_ℂ with hs
  have hs0 : s ≠ 0 := by
    intro h0; apply hn
    have : (starRingEnd ℂ) c0 * ⟪l a, ξ⟫_ℂ * (c0' * ⟪ξ', l' b⟫_ℂ) = (starRingEnd ℂ) c0 * c0' * s := by
      rw [hs]; ring
    rw [this, h0, mul_zero]

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  have ht0 : t ≠ 0 := by
    rw [ht]; exact_mod_cast (norm_ne_zero_iff.mpr hv0ne)
  have hcN : (A.cN : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hA.2.2.2.2.2.2.2.1)
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK10 : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero hcN) (mul_ne_zero hc0ne ht0)) ?_
    exact (map_ne_zero _).mpr (mul_ne_zero hc0ne' ht0)
  have hw1 : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    exact_mod_cast (ne_of_gt (Formalism.L2.S.Pv.AmpOrbCoef.fdegH_pos hA.1 hA.2.1 hG hw1))
  refine ⟨dg * s * K1⁻¹, mul_ne_zero (mul_ne_zero hdg0 hs0) (inv_ne_zero hK10), ?_⟩
  intro γ μR νR ν hCD
  obtain ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩ := hCD
  have hCD' : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨bb, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD' hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD' bb hb0 hbm hbi a b hka hkb ξ ξ'
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae

  have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν := hAmp
  have e1 : OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν =
      dg • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
    rw [hAmp']; exact (smul_inv_smul₀ hdg0 _).symm
  have e2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = K1⁻¹ • A.J νR γ := by
    rw [hJ1, smul_smul, inv_mul_cancel₀ hK10, one_smul]
  rw [e1, e2]
  simp only [smul_smul, mul_assoc]
  rfl

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem ampVec_carrier (hJ : PI.BesselMapUniq.BesselMapUniq) {D : D7} (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} {C : Formalism.L2.SG.LocWSOf.Choice X θ} (hB : Formalism.L2.SG.LocWSOf.WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hTT : HypTT D u u')
    (hW : GoodW D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ))
    (hA : GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (a b : X.B.H (Formalism.L2.SG.LocWSOf.vOf X τ)) (ξ : X.Vloc u (Formalism.L2.SG.LocWSOf.vOf X τ))
    (ξ' : X.Vloc u' (Formalism.L2.SG.LocWSOf.vOf X τ)) (c : ℂ) (hpin : CoefPin hB u u' τ a b ξ ξ' c)
    (hscl : Formalism.L2.SG.LocWSOf.sclOf hB u u' τ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ)
        (Formalism.L2.SG.LocWSOf.locS hB u u' τ) hW hA hT hT') (Formalism.L2.SG.LocWSOf.locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)
          hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (Formalism.L2.SG.LocWSOf.sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν =
        κ • (Formalism.L2.SG.LocWSOf.locS hB u u' τ).J νR γ := by
  obtain ⟨hka, hkb, hn1, -⟩ := hpin
  have hn : ⟪(Formalism.L2.SG.LocWSOf.locS hB u u' τ).B a, ξ⟫_ℂ * ⟪ξ', (Formalism.L2.SG.LocWSOf.locS hB u u' τ).B' b⟫_ℂ ≠ 0 := by
    show ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
      ⟪ξ', Formalism.L2.SG.LocWSOf.sclOf hB u u' τ • Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ ≠ 0
    rw [inner_smul_right]
    have e : ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
        (Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) =
        Formalism.L2.SG.LocWSOf.sclOf hB u u' τ *
          (⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) := by ring
    rw [e, hn1, mul_one]
    exact hscl
  have hl : l1dist (lamD D τ) (lamD D τ) ≤ (0 : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
    simp [l1dist]
  exact ampVec_gen (Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ) Formalism.FourierDecayAlt.P.admissible_atomic_form_one
    Formalism.L2.SG.AmpOrbClosed.amplitude_K_finite Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith))
    (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith)) hH τ u u' hTT θ _ hW (lamD D τ) hl _ hA
    hT hT' a b ξ ξ' hka hkb hn

end Formalism.L2.SG.Pf.CarrierT
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

abbrev gB (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MatKR D.R.k D.R.rS := trG (C.Q τ) (C.Qi τ) γ

abbrev muRB (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Measure (Mt D.R.k D.R.rS) :=
  μRv.map (fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ

theorem torS_inv_mulVec_Wb {z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : inWb D.R.k D.R.rS z) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ D.R.k D.R.rS *ᵥ z = z := by
  rw [torS_muT_inv, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, tTi_mulVec_Wb hz, Matrix.mulVec_smul,
    dMi_mulVec_wb hz, smul_smul, Complex.star_def, map_pow, Complex.conj_I, ← mul_pow, mul_neg, Complex.I_mul_I,
    neg_neg, one_pow, one_smul]

theorem zc_vOf_eq_zB_of_inWb (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hz : inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    zc X C u (vOf X τ) = ((1 : ℝ) : ℂ) • zB X (C.Qi τ) u τ := by
  unfold zB at hz
  unfold zc Qic Qics zB
  rw [pl_vOf, ← Matrix.mulVec_mulVec]
  rw [torS_inv_mulVec_Wb hz]
  simp

theorem baseOf_pi (u : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    πc X C u (vOf X τ) m = piB X (C.Q τ) (C.Qi τ) u τ (tT D.R.k D.R.rS * cjI D.R.k D.R.rS (kaB D)⁻¹ 1 m *
      tTi D.R.k D.R.rS) := by
  unfold πc piB Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conjI]
  simp only [Matrix.mul_assoc]

def tN (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ENNReal := κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1))

def lamPl (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) : ℂ :=
  ((cO : ℂ)⁻¹ * scl * κ * ((tN D θ κ₀ * tN D θ κ₀).toReal : ℂ))⁻¹

theorem tN_toReal_ne (D : D7) (θ : ℝ) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) :
    (tN D θ κ₀ * tN D θ κ₀).toReal ≠ 0 := by
  have hd : ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (deltaN_pos (inv_pos.mpr (kaB_pos D)) one_pos)).ne'
  have hs0 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ 0 := mul_ne_zero hk0 hd
  have hs1 : kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have ht0 : tN D θ κ₀ ≠ 0 := by unfold tN; exact ENNReal.div_ne_zero.mpr ⟨h0, hs1⟩
  have ht1 : tN D θ κ₀ ≠ ⊤ := by unfold tN; exact ENNReal.div_ne_top h1 hs0
  exact ENNReal.toReal_ne_zero.mpr ⟨mul_ne_zero ht0 ht0, ENNReal.mul_ne_top ht1 ht1⟩

theorem pinPlace (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (F : MatKR D.R.k D.R.rS → (X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)))
    (κ : ℂ)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') F γ ν =
        κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ)) (muStd (kaB D) (muRB C τ μRv))
                (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) F) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹ •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
          Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have e2 := hAmp (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB hcell
  obtain ⟨hgU, -, -, hrel, hH, hq, -⟩ := hcell
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hc : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').c =
      ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  have hBz : (baseOf X C u u' (vOf X τ)).z =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z :=
    zc_vOf_eq_zB_of_inWb C u u' τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz.1
  have hBz' : (baseOf X C u u' (vOf X τ)).z' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).z' :=
    zc_vOf_eq_zB_of_inWb C u' u τ (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'.1
  have hBπ : (baseOf X C u u' (vOf X τ)).π =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π := by
    funext m; exact baseOf_pi C u τ m
  have hBπ' : (baseOf X C u u' (vOf X τ)).π' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).π' := by
    funext m; exact baseOf_pi C u' τ m
  have hBW : (baseOf X C u u' (vOf X τ)).μW =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW := hWc
  have hBW' : (baseOf X C u u' (vOf X τ)).μW' =
      (stdL (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D) (kaB_pos D)).μW' :=
    hWc'
  have hBN : (baseOf X C u u' (vOf X τ)).μN = haarLie (Nset D.R.k D.R.rS) κ₀ := hN
  have : SFinite (muRB C τ μRv) := by have := hH.1; infer_instance
  have e3 := orbJ_std (k_pos D) (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (kaB D) (kaB_pos D) hc hk0 ENNReal.ofReal_ne_top κ₀ h0 h1 (baseOf X C u u' (vOf X τ)) hBz hBz' hBπ hBπ' hBW hBW' hBN
    (gB C τ γ) hgU hrel (muRB C τ μRv) hH.2.2.1 hH.2.1 νB hq F hcut
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq C hB u u' τ γ ν hG
  have hs : (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').κN = kapN D θ := rfl
  rw [hs] at e3
  refine e3.trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • Y) e2).trans ?_
  refine (congrArg (fun Y => ((κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)) *
            (κ₀ / (kapN D θ * ENNReal.ofReal (deltaN D.R.k D.R.rS (kaB D)⁻¹ 1)))).toReal : ℂ) • κ • Y) e1).trans ?_
  have key : ∀ (a b c : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • c • Y = (a * b * c) • Y :=
    fun a b c Y => by rw [smul_smul, smul_smul]
  refine (key _ _ _ _).trans ?_
  congr 1
  rw [lamPl, inv_inv]
  unfold tN
  ring

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPin

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem choose_congr {α : Sort*} {p q : α → Prop} (e : p = q) (h : ∃ x, p x) (h' : ∃ x, q x) :
    h.choose = h'.choose := by
  subst e; rfl

theorem orbIntegrand_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p = c • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand Formalism.FourierDecayAlt.B.rho
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem orbJ_smulF (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) {c : ℂ} (hc : c ≠ 0) :
    Formalism.FourierDecayAlt.D.orbJ D γ μ (fun g => c • F g) = c • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  have hP : (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
      (fun θ => Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS) := by
    funext θ
    have e : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
        c • (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := by
      funext p; rw [orbIntegrand_smul, smul_comm]; rfl
    rw [e, integrable_smul_iff hc]
  have e2 : ∀ θ : Formalism.FourierDecayAlt.B.SS k r → ℝ, (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) =
      fun p => c • (θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) := fun θ => by
    funext p; rw [orbIntegrand_smul, smul_comm]
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dif_pos h1, dif_pos h2, choose_congr hP h1 h2, e2, integral_smul]
  · have h1 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS := by
      rw [show (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ (fun g => c • F g) p) D.μSS) =
        ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS from congrArg Exists hP]
      exact h2
    rw [dif_neg h1, dif_neg h2, smul_zero]

end Lin

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def PinCovS (P : Parts X u u') (lam : InfinitePlace X.B.I.F → ℂ) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v)) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    PinHyp P v γ μRv ν →
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ) =
      lam v • ((P.eP v).toContinuousLinearEquiv : _ →L[ℂ] X.Vloc u v).comp
        ((Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) γ) (trMeas P v μRv)
            (P.f (P.τ.symm v))).comp
          ((P.eQ v).symm.toContinuousLinearEquiv : X.Vloc u' v →L[ℂ] _))

def PinCovE (P : Parts X u u') : Prop := ∃ lam : InfinitePlace X.B.I.F → ℂ, (∀ v, lam v ≠ 0) ∧ PinCovS P lam

def rescale (P : Parts X u u') (c : Fin P.S.f → ℂ) : Parts X u u' :=
  { P with f := fun j g => c j • P.f j g }


end Formalism.L2.SG.Pf.Carrier.CarPin
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def fcAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) :
    X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ) :=
  Formalism.L2.SG.Pf.CarrierT.coef0 X C u u' τ a b ξ ξ' c
    (torS (muT D) D.R.k D.R.rS * g * torS (muT D)⁻¹ D.R.k D.R.rS)

theorem gStd_eq (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := by
  unfold Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conj]
  simp only [gB, trG, Matrix.mul_assoc]

theorem measurable_trG {τ : D.what₂.Tau} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (h2 : Q * Qi = 1) :
    Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (trG Q Qi γ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  (Formalism.L2.SG.Pf.WuBL.trG_closedEmb' (Formalism.L2.SG.Pf.Choice.n_eq' X) _ h2).measurable

theorem muStd_eq (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    muStd (kaB D) (muRB C τ μRv) =
      μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)) := by
  have hQ := (C.isT τ).2.1
  have hQc : Qc X C (vOf X τ) * Qic X C (vOf X τ) = 1 := (transpC X C (vOf X τ)).2.1
  unfold muStd muRB
  rw [← cAE_coe, ← cjE_coe (inv_pos.mpr (kaB_pos D)) one_pos,
    Measure.map_map (cAE D.R.k D.R.rS).measurable (measurable_trG hQ),
    Measure.map_map (cjE (k := D.R.k) (r := D.R.rS) (inv_pos.mpr (kaB_pos D)) one_pos).measurable
      ((cAE D.R.k D.R.rS).measurable.comp (measurable_trG hQ))]
  congr 1
  funext x
  show cjT D.R.k D.R.rS (kaB D)⁻¹ 1 (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))) = _
  funext i j
  show cj D.R.k D.R.rS (kaB D)⁻¹ 1 (Matrix.of (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x)))) i j = _
  rw [of_cA, ← gStd_eq C τ x]
  rfl

theorem fcAt_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) :
    fcAt C u u' τ a b ξ ξ' c = fun g => c • stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') g := by
  funext g
  unfold fcAt Formalism.L2.SG.Pf.CarrierT.coef0
  rw [torS_conjI]
  rfl

theorem lamPl_ne (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) (hcO : cO ≠ 0) (hscl : scl ≠ 0) (hκ : κ ≠ 0)
    (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) : lamPl cO scl κ D θ κ₀ ≠ 0 := by
  unfold lamPl
  have hs := tN_toReal_ne D θ κ₀ h0 h1 hk0
  refine inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) hscl) hκ) ?_)
  · exact_mod_cast hcO
  · exact_mod_cast hs

theorem pinAt (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hc0 : c ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν = κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hcO : cOf hB u τ ≠ 0) (hscl : sclOf hB u u' τ ≠ 0)
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ))
        (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ) (fcAt C u u' τ a b ξ ξ' c) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) •
        Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
          (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
          (fcAt C u u' τ a b ξ ξ' c) := by
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hl := lamPl_ne (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ hcO hscl hκ h0 h1 hk0
  rw [fcAt_eq C hB u u' τ hW hA hT hT' a b ξ ξ' c] at hcut ⊢
  rw [← gStd_eq C τ γ, ← muStd_eq C τ μRv] at hcut ⊢
  obtain ⟨θ', hθ', hint⟩ := hcut
  have hcut' : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
          (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)
        (baseOf X C u u' (vOf X τ)).μSS := by
    refine ⟨θ', hθ', ?_⟩
    have h : Integrable (c • (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
          (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
            (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)) (baseOf X C u u' (vOf X τ)).μSS := by
      refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (congrArg (fun Y => θ' p • Y) (Formalism.L2.SG.Pf.Carrier.CarPin.orbIntegrand_smul (baseOf X C u u' (vOf X τ))
        (gStd (kaB D) (gB C τ γ)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
          (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) c p)).trans (smul_comm _ _ _)
    exact (integrable_smul_iff hc0 _).mp h
  have hP := pinPlace C hB u u' τ hW hA hT hT' _ κ hAmp κ₀ h0 h1 hN hWc hWc' γ μRv ν νB hcell hG hcut'
  have hS := Formalism.L2.SG.Pf.Carrier.CarPin.orbJ_smulF (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
    (muStd (kaB D) (muRB C τ μRv)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) hc0
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • Y) hS.symm)
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • c • Y) hP.symm)
  have key : ∀ (a b d : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • d • Y = (a * b * d) • Y :=
    fun a b d Y => by rw [smul_smul, smul_smul]
  refine Eq.trans ?_ (key _ _ _ _).symm
  have e1 : lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹ * c * (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹
      = 1 := by field_simp
  rw [e1, one_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end
