import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists

section
noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.RMeasP

theorem rset_matGroup {k r : ℕ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : IsUnit g₀.det) :
    PI.IsMatGroup (Formalism.MainNotions.S.Rset k r g₀) := by
  have hui : IsUnit (g₀⁻¹).det := Matrix.isUnit_nonsing_inv_det g₀ hu
  have hc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hui
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset k r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_ofPred_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hset]
  exact ⟨hc.closed, hc.one_mem, hc.mul_mem, fun a ha => ⟨hc.inv_mem a ha, Matrix.mul_nonsing_inv a (hc.unit a ha)⟩⟩

theorem isHaarOn_smul' {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : Formalism.MainNotions.S.IsHaarOn S μ) {c : ℝ≥0∞} (h0 : c ≠ 0) (h1 : c ≠ ⊤) : Formalism.MainNotions.S.IsHaarOn S (c • μ) := by
  unfold Formalism.MainNotions.S.IsHaarOn at h ⊢
  obtain ⟨hs, hne, hnull, hinv⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · first
      | infer_instance
      | (rw [← ENNReal.coe_toNNReal h1, ← ENNReal.smul_def]; infer_instance)
  · first
      | exact smul_ne_zero h0 hne
      | (intro hz
         apply hne
         have hu := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) hz
         simp [h0] at hu
         first
           | exact hu
           | exact Measure.measure_univ_eq_zero.mp hu)
  · rw [Measure.smul_apply, hnull, smul_zero]
  · intro s hs'
    rw [Measure.map_smul, hinv s hs']

theorem rMeas_exact (D : D7) (W : LocW D.R.k D.R.rS) (hz : inWb D.R.k D.R.rS W.z) (hT : 0 < Tz D.R.k D.R.rS W.z)
    (hz' : inWb D.R.k D.R.rS W.z') (hT' : 0 < Tz D.R.k D.R.rS W.z')
    (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG) (p : Point ℂ (D.R.rS + 1)) (g₀ : MatKR D.R.k D.R.rS)
    (hg : g₀ ∈ UH (Hpk D.R.k D.R.rS)) (hZ : Formalism.MainNotions.S.ZhatO D.R.k D.R.rS W.z W.z' g₀ = ptMat p) :
    ∃ ν, RMeas D W g₀ 1 ν := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨μ₀', c, hH, hc0, hc1, hmap⟩ :=
    Formalism.L2.SG.Pf.RootHaarLoc.locRootHaar D.R.k D.R.rS hk W.z W.z' hz hT hz' hT' p g₀ hg hZ
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) with hK
  have hu : IsUnit g₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed D.R.k D.R.rS).unit g₀ hg
  by_cases hK0 : K = 0
  ·

    exfalso
    have hka : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
      have h1 : 0 < D.host.ka := by
        unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
        have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
          abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
        have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
        positivity
      have h2 : 0 < gg D := by
        unfold gg
        have a := (D.host.g_prime 0).pos
        have b := (D.host.g_prime 1).pos
        positivity
      positivity
    rw [hK, ENNReal.ofReal_eq_zero] at hK0
    exact absurd hK0 (not_le.2 (pow_pos hka _))
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  set μ₀ : Measure (Mt D.R.k D.R.rS) := (K * c⁻¹) • μ₀' with hμ₀
  have hKc0 : K * c⁻¹ ≠ 0 := mul_ne_zero hK0 (ENNReal.inv_ne_zero.2 hc1)
  have hKc1 : K * c⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hKt (ENNReal.inv_ne_top.2 hc0)
  have hH0 : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀) μ₀ := isHaarOn_smul' hH hKc0 hKc1
  have hmap0 : μ₀.map (rootCoords D.R.k D.R.rS W.z' p) = K • volume := by
    rw [hμ₀, Measure.map_smul, hmap, smul_smul, mul_assoc, ENNReal.inv_mul_cancel hc0 hc1, mul_one]
  have hid : μ₀.map (fun x => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = μ₀ := by
    have : (fun x : Mt D.R.k D.R.rS => fun i j => ((1 : MatKR D.R.k D.R.rS)⁻¹ * Matrix.of x * 1) i j) = id := by
      funext x i j
      simp
    rw [this, Measure.map_id]
  have hN1 : (1 : MatKR D.R.k D.R.rS) ∈ Nset D.R.k D.R.rS := (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS).one_mem
  have hsub : Formalism.MainNotions.S.Rset D.R.k D.R.rS g₀ ⊆ UH (Hpk D.R.k D.R.rS) := fun x hx => hx.1.1
  obtain ⟨ν, hν⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotM_exists (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group D.R.k D.R.rS)
    (rset_matGroup hu) hsub hG hH0
  refine ⟨ν, p, μ₀, ⟨1, hN1, 1, hN1, g₀, by simp, hZ, μ₀, hH0.2.2.1, ?_, hid.symm⟩, ?_⟩
  · rw [hmap0]
  · rw [ENNReal.ofReal_one, one_smul]
    exact hν

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

theorem rMeasExP_of_goodW (hW : ∀ τ, GoodW D τ u u' θ (locW C u u' τ)) : Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C := by
  intro w _ hrep τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  exact rMeas_exact D (locW C u u' τ) h3 (by rw [h5]; exact hTu) h4 (by rw [h6]; exact hTu') h7
    (ptLoc D τ w) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)
    (Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _)
    (Formalism.L2.SG.Pf.RelPtR.zhatO_gamP C u u' w hrep τ)

end Formalism.L2.SG.Pf.RMeasP
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowRestR {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.RMeasExP u u' C ∧ Formalism.L2.SG.Pf.JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)


def RowRestUnifR : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → RowRestR large₂ Y u u' ν C1 Cn Ire



theorem theoremB_uniform_rotated (h : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform) : JointNormBoundRotatedUniform := by
  exact h


def AmplitudeMeasureBounds {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    Formalism.L2.SG.Pf.JointAmplitudePoints.LocalAmplitudesPositive Y u u' ν C hB ∧ Formalism.L2.SG.Pf.JointAmplitudePoints.ThetaWinP Y u u' ν C hB large₂ C1 ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)


def AmplitudeMeasureBoundsUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeMeasureBounds large₂ Y u u' ν C1 Cn Ire


end Formalism.L2.SG.Pf.ThmBChain
end
end
