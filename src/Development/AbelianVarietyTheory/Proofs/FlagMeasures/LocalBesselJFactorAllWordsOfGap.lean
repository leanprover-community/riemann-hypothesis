import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LiftOntoCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegral

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pinAll_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' :=
  fun _ _ _ u u' => Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u'

end GlobalTheory
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevantLift_normalisedData_exist : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' := by
  atlas_forward_decl GlobalTheory.pinAll_all
end

section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.SlocTie

def rmulE {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1) (hba : b * a = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun x := Matrix.of.symm (Matrix.of x * a)
  invFun x := Matrix.of.symm (Matrix.of x * b)
  left_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * a)) * b) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hab, Matrix.mul_one]; rfl
  right_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * b)) * a) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hba, Matrix.mul_one]; rfl
  measurable_toFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop
  measurable_invFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop

theorem quot_rmul {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1)
    (hba : b * a = 1) {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : μG.map (rmulE a b hab hba) = μG)
    (hq : IsQuotMeas μG μS ν) : IsQuotMeas μG μS (ν.map (rmulE a b hab hba)) := by
  intro f hf
  set R := rmulE a b hab hba
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f x ∂(μG.map R) := by rw [hG]
    _ = ∫⁻ x, f (R x) ∂μG := MeasureTheory.lintegral_map_equiv _ R
    _ = ∫⁻ x, (∫⁻ s, f (R (fun i j => (Matrix.of s * Matrix.of x) i j)) ∂μS) ∂ν := hq _ (hf.comp R.measurable)
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (R x)) i j) ∂μS) ∂ν := by
        refine lintegral_congr fun x => lintegral_congr fun s => ?_
        congr 1
        show Matrix.of.symm (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) * a) =
          fun i j => (Matrix.of s * Matrix.of (Matrix.of.symm (Matrix.of x * a))) i j
        rw [Equiv.apply_symm_apply]
        funext i j
        show (Matrix.of s * Matrix.of x * a) i j = (Matrix.of s * (Matrix.of x * a)) i j
        rw [Matrix.mul_assoc]
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂(ν.map R) :=
        (MeasureTheory.lintegral_map_equiv (fun x => ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) R).symm

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def yInv (C : Choice X θ) (τ : D.what₂.Tau) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS

theorem y_inv (C : Choice X θ) (τ : D.what₂.Tau) : C.y τ * yInv C τ = 1 ∧ yInv C τ * C.y τ = 1 := by
  obtain ⟨-, hi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem (C.y τ) (C.y_mem τ)
  exact ⟨(Matrix.mul_eq_one_comm_of_card_eq (Fin _) (Fin _) ℂ rfl).mp hi, hi⟩

def Ry (C : Choice X θ) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  rmulE (C.y τ) (yInv C τ) (y_inv C τ).1 (y_inv C τ).2

theorem muGB_rinv (C : Choice X θ) (τ : D.what₂.Tau) :
    (muGB X (C.Q τ) (C.Qi τ) τ).map (Ry C τ) = muGB X (C.Q τ) (C.Qi τ) τ := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hy', Formalism.L2.SG.Pf.Choice.qiHqi _ h2 hg]
  set γy := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * C.y τ * C.Qi τ) hJ
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  have he := eT_emb C τ (vOf X τ)
  have hcomm : (Ry C τ) ∘ eT C τ (vOf X τ) = eT C τ (vOf X τ) ∘ (fun γ => γ * γy) := by
    funext γ
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (C.Qi τ * uMat γ * C.Q τ)) * C.y τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ * γy) * C.Q τ)
    rw [Equiv.apply_symm_apply, show uMat (γ * γy) = uMat γ * uMat γy from rfl,
      show uMat γy = C.Q τ * C.y τ * C.Qi τ from rfl]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one]
  show ((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))).map (Ry C τ) =
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))
  rw [Measure.map_map (Ry C τ).measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (measurable_mul_const γy), map_mul_right_eq_self]

def shiftC (C : Choice X θ) : Choice X θ :=
  { C with
    nuS := fun u τ => (C.nuS u τ).map (Ry C τ)
    nuS_q := fun u τ => quot_rmul _ _ _ _ (muGB_rinv C τ) (C.nuS_q u τ) }

theorem loc_main (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        l2SG (C.nuS u τ) (phiOf hB u τ) := by
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  refine ⟨β, hβm, hβ1, ?_⟩
  have hid := loc_id (shiftC C) u τ hβm hβ1
  rw [hid]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ)
    (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  show ∫⁻ x, (‖wT C u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂((C.nuS u τ).map (Ry C τ)) =
    ∫⁻ x, (‖phiOf hB u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂(C.nuS u τ)
  rw [MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]
  rfl

end GlobalTheory.SlocTie
end
end

section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau), ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧ (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧ ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
  first | exact @GlobalTheory.SlocTie.loc_main | exact GlobalTheory.SlocTie.loc_main | (intros; apply GlobalTheory.SlocTie.loc_main <;> assumption)
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  atlas_forward_decl GlobalTheory.MuNPi.muN_eq_pi_muNl
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.MuHPi

theorem hloc_eq_HGv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.Pf.WuDec.Hloc X u v =
      (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := by
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  rfl

theorem muH_eq_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muHl C u (X.pl v) v) (Formalism.L2.SG.Pf.WuDec.Hloc X u v) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muHl C u τ w) (Formalism.L2.SG.Pf.WuDec.Hloc X u w) := by
      rintro τ _ rfl; exact invOn_muHl C u τ
    intro v
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_coe] at hc hi
  refine Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG X u)
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG, Subgroup.coe_pi]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_conc _ _ fun v => by rw [← hloc_eq_HGv]; exact (hloc v).2.2.1
  · intro g hg
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v)
      (by rw [hloc_eq_HGv]; exact hg v (Set.mem_univ v))
  · exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuHPi
end
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  atlas_forward_decl GlobalTheory.MuHPi.muH_eq_pi
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section
namespace GlobalTheory.MuSPi

theorem muNH_prod_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  intro D X θ C u κN κH hN hH
  have hsN : ∀ v, SigmaFinite (muNl C (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ _ rfl; exact sf_muNl C τ (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ)
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsH : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsM : ∀ v, SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl; exact (invOn_mulMap C u τ).1
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  congr 1
  have mp := Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurePreserving_piProd (fun v => muNl C (X.pl v) v) (fun v => muHl C u (X.pl v) v)
  rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
    mp.measurable]
  haveI : ∀ v, SigmaFinite (((muNl C (X.pl v) v).prod (muHl C u (X.pl v) v)).map
      (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hsM
  exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
    (fun v => measurable_mul.aemeasurable)

end GlobalTheory.MuSPi
end
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentSubgroupHaarProduct_eq_pi_localImage : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  atlas_forward_decl GlobalTheory.MuSPi.muNH_prod_pi
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem weil_bruhatProd_normSq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  intro D X u κ M hMs hS β hβm hβ1
  haveI := hMs
  obtain ⟨hNsf, -, hN0, -⟩ := X.muN_haar u
  obtain ⟨hHsf, -, hH0, -⟩ := X.muH_haar u
  haveI := hNsf
  haveI := hHsf
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  have hSmeas : MeasurableSet (X.SinfU u) := (Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u).measurableSet
  have hae : ∀ᵐ s ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)), s ∈ X.SinfU u := by
    refine (ae_map_iff (p := fun s => s ∈ X.SinfU u) hmul.aemeasurable hSmeas).2 ?_
    have h1 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun s => s ∈ X.NinfU u) (by rw [ae_iff]; exact hN0)
    have h2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun s => s ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}))
        (by rw [ae_iff]; exact hH0)
    filter_upwards [h1, h2] with p hp1 hp2
    exact Formalism.L2.SG.WuDecayPf.mul_mem_sinfU X u p.1 p.2 hp1 hp2
  have hβprod : Measurable (fun x : X.B.I.Ginf => ∏ v, β v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hβm v).comp (measurable_pi_apply v)
  have hWm : Measurable (fun x : X.B.I.Ginf => ‖X.Wu u x‖ₑ ^ 2) :=
    (X.Wu_spec u).2.2.1.enorm.measurable.pow_const 2
  have hfm : Measurable (fun x : X.B.I.Ginf => (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2) := hβprod.mul hWm
  rw [X.nuQ_weil u _ hfm]
  have hin : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
      ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = κ * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    have e1 : ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
        ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
        ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u x‖ₑ ^ 2
          ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with s hs
      rw [← enorm_norm (X.Wu u (s * x)), Formalism.L2.SG.Pf.WuDec.norm_Wu_inv X u s hs x, enorm_norm]
    rw [e1, lintegral_mul_const _ (show Measurable (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) from
      hβprod.comp (measurable_mul_const x)), hS, lintegral_smul_measure]
    have e2 : ∫⁻ s, ∏ v, β v ((s * x) v) ∂(Measure.pi M) = 1 := by
      have e3 : (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) = fun s => ∏ v, β v (s v * x v) := rfl
      rw [e3, QPK.lintegral_fintype_prod (fun v s => β v (s * x v))
        (fun v => (hβm v).comp (measurable_mul_const _))]
      simp [hβ1]
    rw [e2, smul_eq_mul, mul_one]
  simp only [hin]
  rw [lintegral_const_mul _ hWm, (X.Wu_spec u).2.2.2.2, mul_one]

end GlobalTheory
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_besselNormSq_bruhatProduct : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  atlas_forward_decl GlobalTheory.weil_bruhatProd_normSq
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem pi_muNl_eq_dnB_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  intro D X θ C A hθ _hA
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ w rfl
      exact sf_muNl C τ hθ
    intro v
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  obtain ⟨hemb, hmap⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have h := congrArg (fun μ => μ (Formalism.L2.SG.LoopTerm.trInf C '' A)) hmap
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  exact h

end GlobalTheory
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_pulledBack_unipotentMeasure_eq_besselImage : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  atlas_forward_decl GlobalTheory.pi_muNl_eq_dnB_image
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem prod_lint (D : D7) (X : HidaSetting D) (u : D.what₂.Word)
    (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hβm : ∀ v, Measurable (β v)) :
    ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hW : ∀ x : X.B.I.Ginf, ‖X.Wu u x‖ₑ ^ 2 = ∏ v, ‖X.Wloc u v (x v)‖ₑ ^ 2 := by
    intro x
    have : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
      rw [← ofReal_norm_eq_enorm, Formalism.L2.SG.Pf.WuDec.norm_Wu,
        ENNReal.ofReal_prod_of_nonneg (fun v _ => norm_nonneg _)]
      simp only [ofReal_norm_eq_enorm]
    rw [this, Finset.prod_pow]
  simp_rw [hW, ← Finset.prod_mul_distrib]
  have : ∀ v, SigmaFinite (Formalism.REAL.muG (X.B.I.ε v)) := fun v => inferInstance
  exact QPK.lintegral_fintype_prod (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v y => β v y * ‖X.Wloc u v y‖ₑ ^ 2)
    (fun v => (hβm v).mul ((X.Wloc_cont u v).enorm.measurable.pow_const 2))

theorem muH_univ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    Measure.pi (fun v => muHl C u (X.pl v) v) Set.univ = 1 := by
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    exact h _ _ (X.pl.symm_apply_apply v)
  rw [Measure.pi_univ]
  refine Finset.prod_eq_one fun v _ => ?_
  have h : ∀ τ w, vOf X τ = w → muHl C u τ w Set.univ = 1 := by
    rintro τ _ rfl
    rw [← Set.preimage_univ (f := eT C τ (vOf X τ)), ← Measure.map_apply (eT_emb C τ _).measurable MeasurableSet.univ,
      map_muHl C u τ, C.muW_one u τ]
  exact h _ _ (X.pl.symm_apply_apply v)

end GlobalTheory.ProductL2

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem l2prod : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  intro D X Y θ C hB u hθ _ _ _
  have key : ∀ v, ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) = 1) ∧
      (∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
        l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) ∧
      SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    intro v
    have h : ∀ τ w, vOf X τ = w → ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        (∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) =
          l2SG (C.nuS u τ) (phiOf hB u τ)) ∧
        SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl
      obtain ⟨β, h1, h2, h3⟩ := GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass D X θ C hB u τ
      exact ⟨β, h1, h2, h3, (invOn_mulMap C u τ).1⟩
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  choose β hβm hβ1 hβl hsf using key
  obtain ⟨κN, hN0, hNt, hN⟩ := GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures D X θ C u
  obtain ⟨κH, hH0, hHt, hH⟩ := GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures D X θ C u
  have hS := GlobalTheory.T.unipotentSubgroupHaarProduct_eq_pi_localImage D X θ C u κN κH hN hH
  have hW := GlobalTheory.T.weil_formula_besselNormSq_bruhatProduct D X u (κN * κH) _ hsf hS β hβm hβ1
  rw [prod_lint D X u β hβm] at hW
  simp only [hβl] at hW
  have hP : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = κN * κH := by
    rw [← hW]; exact (Equiv.prod_comp X.pl (fun τ => l2SG (C.nuS u τ) (phiOf hB u τ))).symm
  have hP0 : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := by rw [hP]; exact mul_ne_zero hN0 hH0
  have hPt : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by rw [hP]; exact ENNReal.mul_ne_top hNt hHt
  have hne0 : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := fun τ =>
    (Finset.prod_ne_zero_iff.1 hP0) τ (Finset.mem_univ τ)
  have hnet : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by
    intro τ ht
    apply hPt
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ht]
    exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun τ' _ => hne0 τ')
  refine ⟨fun τ => ENNReal.toReal_pos (hne0 τ) (hnet τ), ?_⟩
  rw [← ENNReal.toReal_prod, hP, ← GlobalTheory.T.pi_pulledBack_unipotentMeasure_eq_besselImage D X θ C (Y.FN u) hθ (Y.FN_fund u).1, hN, hH,
    Measure.smul_apply, Measure.smul_apply, muH_univ D X θ C u]
  simp only [smul_eq_mul, mul_one, ENNReal.toReal_mul]
  ring

end GlobalTheory.ProductL2
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_l2_positive : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  atlas_forward_decl GlobalTheory.ProductL2.l2prod
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmplitudeConst

theorem normSq_inv_mul_sqrt (l d l' d' : ℝ) (hl : 0 < l) (hl' : 0 < l') (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    Complex.normSq ((((l / d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (l / d * d' / l') : ℝ) : ℂ)) = d / l * (d' / l') := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.normSq_ofReal]
  have hs : 0 ≤ l / d * d' / l' := by positivity
  have e : (l / d)⁻¹ * Real.sqrt (l / d * d' / l') * ((l / d)⁻¹ * Real.sqrt (l / d * d' / l')) =
      (l / d)⁻¹ * (l / d)⁻¹ * (Real.sqrt (l / d * d' / l') * Real.sqrt (l / d * d' / l')) := by ring
  rw [e, Real.mul_self_sqrt hs]
  rcases hd.eq_or_lt with h | h
  · subst h; simp
  · field_simp

theorem const_eq (P P' L L' K M H M' H' V V' : ℝ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hM' : 0 < M')
    (hH' : 0 < H') (hL : 0 < L) (hL' : 0 < L') (hV : L * V = M * H) (hV' : L' * V' = M' * H')
    (hP : 0 ≤ P) (hP' : 0 ≤ P') :
    P / L * (P' / L') = ((Real.sqrt (K * M * H / P * (K * M' * H' / P')))⁻¹ * K) ^ 2 * (V * V') := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_inv, inv_div, inv_div]
  have eV : V = M * H / L := by field_simp; linarith
  have eV' : V' = M' * H' / L' := by field_simp; linarith
  subst eV eV'
  field_simp

theorem prod_finrank_loc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ τ : D.what₂.Tau, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) = (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl

theorem prod_normSq_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  intro D X Y hF θ C hB u u' hθ hG
  have hK0 : 0 ≤ X.volK2 := ENNReal.toReal_nonneg
  have hv := hF.volPos u
  have hv' := hF.volPos u'
  have hN : 0 < X.volK2 * (X.muN u (Y.FN u)).toReal := hv.1
  have hN' : 0 < X.volK2 * (X.muN u' (Y.FN u')).toReal := hv'.1
  have hK : 0 < X.volK2 := pos_of_mul_pos_left hN ENNReal.toReal_nonneg
  have hNu : 0 < (X.muN u (Y.FN u)).toReal := pos_of_mul_pos_right hN hK0
  have hNu' : 0 < (X.muN u' (Y.FN u')).toReal := pos_of_mul_pos_right hN' hK0
  have hHu : 0 < (X.muH u Set.univ).toReal := hv.2
  have hHu' : 0 < (X.muH u' Set.univ).toReal := hv'.2
  obtain ⟨hl, hp⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u hθ hG hNu hHu
  obtain ⟨hl', hp'⟩ := GlobalTheory.T.product_l2_positive D X Y θ C hB u' hθ hG hNu' hHu'
  have hτ : ∀ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) =
      (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) / (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal *
        ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) := by
    intro τ
    unfold sclOf cOf
    exact normSq_inv_mul_sqrt _ _ _ _ (hl τ) (hl' τ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_div_distrib, prod_finrank_loc, prod_finrank_loc]
  unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
  exact const_eq _ _ _ _ _ _ _ _ _ _ _ hK hNu hHu hNu' hHu' (Finset.prod_pos fun τ _ => hl τ)
    (Finset.prod_pos fun τ _ => hl' τ) hp hp' (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.AmplitudeConst
end
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeConstant_eq_prod_covolumes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  atlas_forward_decl GlobalTheory.AmplitudeConst.prod_normSq_eq
end

section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants PI.AmpRootCommon PI.AmpRelAtPt

variable {k r : ℕ}

theorem psi_rel (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : ℂ) (hc : star c = c)
    (p : Point ℂ (r + 1)) (g₀ : MatKR k r) (hg : g₀ ∈ UH (Hpk k r)) (hZ : ZhatO k r z z' g₀ = ptMat p)
    (a : MatKR k r) (ha : a ∈ RStab k r g₀) : psi k r z c a = psi k r z' c (g₀⁻¹ * a * g₀) := by
  have ha' : a ∈ Nset k r ∧ g₀⁻¹ * a * g₀ ∈ Nset k r := ha
  have hsum := sum_super (ptσ_invol p) (zhat_pt hZ) (ptζ_ne p) (fun i i1 h => pt_adj p i i1 h)
    (flagMat_upper (z := z) ha'.1) (flagMat_diag ha'.1) (flagMat_upper (z := z') ha'.2)
    (flagMat_diag ha'.2) (flag_rel hz hz' hg ha)
  have hell : ell k r z' (g₀⁻¹ * a * g₀) = star (ell k r z a) := by
    rw [ell_eq, ell_eq, hsum]
  have hcim : c.im = 0 := Complex.conj_eq_iff_im.mp hc
  have hre : (c * star (ell k r z a)).re = (c * ell k r z a).re := by
    simp [Complex.mul_re, hcim]
  simp only [Formalism.QuantumDeterminants.psi, hell, hre]

theorem psi_conj (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) {n m : MatKR k r}
    (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : psi k r z c (n⁻¹ * m * n) = psi k r z c m := by
  obtain ⟨hone, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have hni : n⁻¹ ∈ Nset k r := hinvN n hn
  have h1 : psi k r z c 1 = 1 := by
    have hmul := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hone hone
    rw [Matrix.one_mul] at hmul
    have hne : psi k r z c 1 ≠ 0 := Complex.exp_ne_zero _
    exact mul_left_cancel₀ hne (hmul.symm.trans (mul_one _).symm)
  have hinv : n⁻¹ * n = 1 := uh_inv_mul hn.1
  have hpair := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hn
  rw [hinv, h1] at hpair
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c (hmulN _ hni _ hm) hn,
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hm]
  calc psi k r z c n⁻¹ * psi k r z c m * psi k r z c n
      = psi k r z c m * (psi k r z c n⁻¹ * psi k r z c n) := by ring
    _ = psi k r z c m := by rw [← hpair, mul_one]

theorem psi_cell (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (c : ℂ) (hc : star c = c) (p : Point ℂ (r + 1)) (γ : MatKR k r)
    (hγ : γ ∈ UH (Hpk k r)) (hcell : IsInCell (ZhatO k r z z' γ) p) {m : MatKR k r} (hm : m ∈ Nset k r)
    (hm' : γ⁻¹ * m * γ ∈ Nset k r) : psi k r z c m = psi k r z' c (γ⁻¹ * m * γ) := by
  obtain ⟨n, hn, n', hn', g₀, hg₀, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep k r z z' γ p hz hz' hT hT' hγ hcell
  obtain ⟨_, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have e1 : n' * n'⁻¹ = 1 := uh_mul_inv hn'.1
  have key : n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹ = g₀⁻¹ * (n⁻¹ * m * n) * g₀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc n' n'⁻¹, e1, Matrix.one_mul, Matrix.mul_one]
  have hnmn : n⁻¹ * m * n ∈ Nset k r :=
    hmulN _ (hmulN _ (hinvN n hn) _ hm) _ hn
  have ha : n⁻¹ * m * n ∈ RStab k r g₀ := by
    refine ⟨hnmn, ?_⟩
    rw [← key]
    exact hmulN _ (hmulN _ hn' _ hm') _ (hinvN n' hn')
  have hback := psi_conj z' hz' c (hinvN n' hn') hm'
  rw [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse e1)] at hback
  calc psi k r z c m = psi k r z c (n⁻¹ * m * n) := (psi_conj z hz c hn hm).symm
    _ = psi k r z' c (g₀⁻¹ * (n⁻¹ * m * n) * g₀) := psi_rel z z' hz hz' c hc p g₀ hg₀ hZ _ ha
    _ = psi k r z' c (n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹) := by rw [key]
    _ = psi k r z' c ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) := hback

end GlobalTheory.StabInv

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WuDec Formalism.L2.SG.Pf.EquivPf Formalism.L2.SG.Pf.Choice

theorem wloc_n {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s x : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ Nloc X u v) :
    X.Wloc u v (s * x) = psiV X u v (uMat s) • X.Wloc u v x := by
  have h1H : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Hloc X u v := by
    intro y _
    rw [uMat_one', Matrix.one_mulVec]
  have h1N : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Nloc X u v := by
    refine ⟨?_, ?_⟩
    · rw [uMat_one']
      exact inS_one
    · intro y _
      rw [uMat_one', sub_self, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  have hA := locEquiv X u v s hs 1 h1H x
  have hB := locEquiv X u v 1 h1N 1 h1H x
  simp only [mul_one] at hA
  simp only [mul_one, one_mul, uMat_one', psiV_one, one_smul] at hB
  rw [hA, ← hB]

theorem uMat_mul_loc {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem stab_inv : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Point ℂ (D.R.rS + 1)), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) p → ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u'))) γ, ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) (s * x)) (X.Wloc u' (vOf X τ) (γ⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) x) (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) := by
  intro D X θ C _ u u' τ γ p _ hrel s hs x
  obtain ⟨hQiQ, hQQi, hgram, hcol⟩ := C.isT τ
  have hs1 : s ∈ Nloc X u (vOf X τ) := hs.1
  have hs2 : γ⁻¹ * s * γ ∈ Nloc X u' (vOf X τ) := hs.2
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := Formalism.L2.SG.Pf.Choice.n_eq' X
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 :=
    fun a => pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have hcolE : ∀ a : Fin D.R.rS, C.Q τ *ᵥ Pi.single (eI D.R.k D.R.rS a) 1 =
      frS D ^ (D.R.rS - (a : ℕ)) • Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.eR a) :=
    fun a => (hcol a a rfl).1
  have hmN : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      C.Qi τ * uMat t * C.Q τ ∈ Nset D.R.k D.R.rS := by
    intro w t ht
    have hU : (uMat t)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat t = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := t.2
    exact nset_loc hn _ _ _ hQiQ hQQi hgram _ _ hc hcolE _ hU ht
  have hpsi : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      psiV X w (vOf X τ) (uMat t) = psiS D (zB X (C.Qi τ) w τ) (C.Qi τ * uMat t * C.Q τ) := by
    intro w t ht
    have hback : C.Q τ * (C.Qi τ * uMat t * C.Q τ) * C.Qi τ = uMat t := by
      simp only [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    have h := Formalism.L2.SG.Pf.psiTr C w τ _ (hmN w t ht)
    rw [hback] at h
    exact h
  set g := Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ with hg
  have hginv : g⁻¹ = C.Qi τ * uMat γ⁻¹ * C.Q τ := by
    apply Matrix.inv_eq_left_inv
    rw [hg, Formalism.L2.SG.RealObj.trG]
    calc C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat γ * C.Q τ)
        = C.Qi τ * (uMat γ⁻¹ * (C.Q τ * C.Qi τ) * uMat γ) * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_inv_mul, Matrix.mul_one, hQiQ]
  have hconj : C.Qi τ * uMat (γ⁻¹ * s * γ) * C.Q τ = g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g := by
    rw [hginv, hg, Formalism.L2.SG.RealObj.trG, uMat_mul_loc, uMat_mul_loc]
    calc C.Qi τ * (uMat γ⁻¹ * uMat s * uMat γ) * C.Q τ
        = C.Qi τ * (uMat γ⁻¹ * 1 * uMat s * 1 * uMat γ) * C.Q τ := by
          rw [Matrix.mul_one, Matrix.mul_one]
      _ = C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat s * C.Q τ) * (C.Qi τ * uMat γ * C.Q τ) := by
          rw [← hQQi]
          simp only [Matrix.mul_assoc]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hz', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hT' : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
    rw [hTz']; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u'
  have hm' : g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g ∈ Nset D.R.k D.R.rS := by
    rw [← hconj]; exact hmN u' _ hs2
  have hkey : psiV X u (vOf X τ) (uMat s) = psiV X u' (vOf X τ) (uMat (γ⁻¹ * s * γ)) := by
    rw [hpsi u s hs1, hpsi u' _ hs2, hconj]
    exact psi_cell _ _ hz hz' hT hT' _ (Complex.conj_ofReal _) p g hrel.1 hrel.2.1 (hmN u s hs1) hm'
  have hx : γ⁻¹ * (s * x) = (γ⁻¹ * s * γ) * (γ⁻¹ * x) := by group
  rw [wloc_n X u (vOf X τ) s x hs1, hx, wloc_n X u' (vOf X τ) _ _ hs2, ← hkey]
  have hnorm : ‖psiV X u (vOf X τ) (uMat s)‖ = 1 := norm_psiR _ _ _ _ _ _
  have hcm : (starRingEnd ℂ) (psiV X u (vOf X τ) (uMat s)) * psiV X u (vOf X τ) (uMat s) = 1 := by
    rw [Complex.conj_mul', hnorm]; norm_num
  ext ξ
  rw [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) ξ) * hcm

end GlobalTheory.StabInv
end

section
universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hl i k).1 hik, zero_mul]
    · rw [(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hl' k i).1 h, mul_zero]
      · rw [(hl i k).1 h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RelPtLift

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem loUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.LowerUnipotentMul.main
  | exact _root_.GlobalTheory.LowerUnipotentMul.main
  | (apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerUnipotentMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerUnipotentMul.main ..)

theorem upUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul ..)

end Uni

variable {k r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Formalism.QuantumDeterminants.Zhat k r z z' g * sgn r := by
  ext a b
  rw [sgn, Matrix.mul_diagonal, mul_comm]
  rfl

theorem upUni_sgn_conj {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsUpUni (sgn r * U * sgn r) := by
  intro a b
  rw [sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hab => by rw [hU0 a b hab]; ring, fun hab => ?_⟩
  subst hab
  rw [hU1, mul_one, ← mul_pow]
  simp

theorem loUni_conjT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsLoUni Uᴴ := by
  intro a b
  refine ⟨fun hab => by rw [conjTranspose_apply, hU0 b a hab, star_zero], fun hab => ?_⟩
  subst hab
  rw [conjTranspose_apply, hU1, star_one]

theorem det_Hpk : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem mem_UH_of_Sset {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z) : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
  Formalism.QuantumDeterminants.Sset_UH ha

theorem zhat_dcoset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hz' : Formalism.QuantumDeterminants.inWb k r z')
    {a a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset k r z') (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c b, b < c → U c b = 0) ∧ (∀ c, U c c = 1) ∧
      (∀ c b, b < c → U' c b = 0) ∧ (∀ c, U' c c = 1) ∧
      Formalism.QuantumDeterminants.Zhat k r z z' (a * g * a'⁻¹) = Uᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * U' := by
  obtain ⟨-, -, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup k r z' hz'
  obtain ⟨U, hU0, hU1, hF⟩ := Formalism.QuantumDeterminants.S_F hz (hinv a ha)
  obtain ⟨U', hU0', hU1', hF'⟩ := Formalism.QuantumDeterminants.S_F hz' (hinv' a' ha')
  have hdet : IsUnit a.det := ((Formalism.QuantumDeterminants.uHGroup _ _ det_Hpk).2.2 a (mem_UH_of_Sset ha)).1
  have hai : (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.Sset_UH (hinv a ha)
  have hHa : Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ * a := by rw [hai]
      _ = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨U, U', hU0, hU1, hU0', hU1', ?_⟩
  rw [Formalism.QuantumDeterminants.Zhat_eq, Formalism.QuantumDeterminants.Zhat_eq]
  calc (Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * g * a'⁻¹) * Formalism.QuantumDeterminants.Fm k r z'
      = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * (Formalism.QuantumDeterminants.Hpk k r * a) * g * (a'⁻¹ * Formalism.QuantumDeterminants.Fm k r z') := by
        simp only [Matrix.mul_assoc]
    _ = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * ((a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r) * g * (Formalism.QuantumDeterminants.Fm k r z' * U') := by
        rw [hHa, hF']
    _ = (a⁻¹ * Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z' * U' := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Uᴴ * ((Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z') * U' := by
        rw [hF, conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem relPt_dcoset (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z)
    (hz' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z') {a a' γ : MatKR D.R.k D.R.rS} (ha : a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z') {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) :
    RelPt D z z' (a * γ * a'⁻¹) p := by
  obtain ⟨hUH, ⟨L, V, hL, hV, hZ⟩, hGf⟩ := h
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup _ _ z' hz'
  have hG := Formalism.QuantumDeterminants.uHGroup _ _ (det_Hpk (k := D.R.k) (r := D.R.rS))
  refine ⟨hG.2.1 _ (hG.2.1 _ (mem_UH_of_Sset ha) _ hUH) _ (mem_UH_of_Sset (hinv' a' ha')), ?_, ?_⟩
  · obtain ⟨U, U', hU0, hU1, hU0', hU1', he⟩ := zhat_dcoset hz hz' ha ha' γ
    have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ = L * ptMat p * V * sgn D.R.rS := by
      rw [← hZ, zhatO_eq, Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    refine ⟨Uᴴ * L, V * (sgn D.R.rS * U' * sgn D.R.rS), loUni_mul (loUni_conjT hU0 hU1) hL,
      upUni_mul hV (upUni_sgn_conj hU0' hU1'), ?_⟩
    rw [zhatO_eq, he, hZ']
    simp only [Matrix.mul_assoc]
  · rw [Formalism.QuantumDeterminants.gInv _ _ z z' hz hz' a ha a'⁻¹ (hinv' a' ha') γ]
    exact hGf

end GlobalTheory.RelPtLift

theorem GlobalTheory.RelPtLift.relPt_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  intro D X Y hF hI θ C u u' t s hs hG hr τ
  obtain ⟨p, hp⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨a, ha, a', ha', heq⟩ := GlobalTheory.TermCoset.dcoset D X Y hF hI θ C u u' t s hs τ
  refine ⟨p, ?_⟩
  rw [heq]
  exact GlobalTheory.RelPtLift.relPt_dcoset D (Formalism.L2.SG.Pf.zTr C u τ).1 (Formalism.L2.SG.Pf.zTr C u' τ).1 ha ha' hp
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevant_term_has_real_relative_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  atlas_forward_decl GlobalTheory.RelPtLift.relPt_lift
end

section
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JFactTie

theorem jFactN_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  intro D X Y hF hI C hB u u' hGap t hG hr
  have hex : ∃ s : TT Y u u', s.toTerm = tc hI t :=
    Formalism.L2.SG.Pf.liftOntoC_of Formalism.L2.SG.Pf.WittFlags.LatIso_holds D X Y u u' (tc hI t)
  have hs : hex.choose.toTerm = tc hI t := hex.choose_spec
  have hrel : hex.choose.relevant := by
    show hex.choose.toTerm.relevant
    rw [hs]
    exact (hI.relevant t).1 hr
  have hsG : hex.choose.G ≠ 0 := by
    show hex.choose.toTerm.G ≠ 0
    rw [hs]
    intro h0
    apply hG
    apply (algebraMap D.host.F D.host.E).injective
    rw [gterm_val hI t, h0, map_zero]
  have hP : HasPin hex.choose := GlobalTheory.T.relevantLift_normalisedData_exist D X Y u u' hex.choose hrel hsG
  have hx := hP.choose_spec
  have hJ : JtOf hI t = Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hex.choose := by
    unfold JtOf; rw [dif_pos hex]
  have hV : volRC hI t = (hP.choose.2.1 hP.choose.2.2).toReal := by
    unfold volRC covR; rw [dif_pos ⟨hr, hG, hex⟩, dif_pos hP]
  have hinv : ∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (hex.choose.pt.1 v), ∀ y,
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * (r * y))) =
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * y)) := by
    intro v
    obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, by simp [vOf]⟩
    obtain ⟨p, hp⟩ := GlobalTheory.T.relevant_term_has_real_relative_point D X Y hF hI 1 C u u' t hex.choose hs hG hr τ
    exact GlobalTheory.StabInv.stab_inv D X 1 C hB u u' τ (hex.choose.pt.1 (vOf X τ)) p hGap hp
  obtain ⟨μl, νl, hH, hQ, hR, hA⟩ := GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local D X Y 1 C u u' hex.choose hP.choose hrel hsG hx.1 hx.2.1 hx.2.2 hinv
  have hloc : ∀ τ, j1 hI C hB t τ = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) *
      hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ))) := by
    intro τ
    haveI : SigmaFinite (μl (vOf X τ)) := (hH (vOf X τ)).1
    exact GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral D X Y hF hI C hB u u' t hex.choose hs hG hr hGap τ (μl (vOf X τ)) (νl (vOf X τ)) inferInstance
      (hQ (vOf X τ)) (hR τ)
  have hK := GlobalTheory.T.amplitudeConstant_eq_prod_covolumes D X Y hF 1 C hB u u' one_pos hGap
  have hre : (∏ τ, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ)))) =
      ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (hex.choose.pt.1 v)) :=
    Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hcov : covN (Y := Y) C u * covN (Y := Y) C u' =
      ((Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := rfl
  rw [hJ, hV, hA, hcov]
  unfold P1
  rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, hre, hK]
  ring

end GlobalTheory.JFactTie
end

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBesselJFactor_all_words_of_gap : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  atlas_forward_decl GlobalTheory.JFactTie.jFactN_all
end
