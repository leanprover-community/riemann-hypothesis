import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section K

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)

def sclV : ℝ :=
  Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ)

def WinK (K : ℝ) : Prop := normWin D large₂ C1 (K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)))

def OOCorePK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) * K = localAmplitudeProduct u u' hB w

def JFactPK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧ J2of Y u u' ν (toPts w) * K = localAmplitudeProduct u u' hB w

theorem jFactPK_of_core (h : OOCorePK Y u u' ν C hB large₂ C1) : JFactPK Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨w', hw', g, hg⟩ := isPtRep_of_J2of hJ
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  rw [Formalism.L2.SG.Pf.OOCore.joint_amplitude_eq_normSq Y u u' ν w' ⟨g, hg⟩]
  exact h w' hb ⟨g, hg⟩

theorem localAmplitudesPositive_of_kernel (h : JFactPK Y u u' ν C hB large₂ C1) : LocalAmplitudesPositive Y u u' ν C hB := by
  intro w hb hJ
  obtain ⟨K, hK, -, e⟩ := h w hb hJ
  rw [← e]
  exact mul_pos hJ hK

theorem thetaWinP_of_K (h : JFactPK Y u u' ν C hB large₂ C1) : ThetaWinP Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨K, hK, hW, e⟩ := h w hb hJ
  have hP : 0 < localAmplitudeProduct u u' hB w := by rw [← e]; exact mul_pos hJ hK
  have e2 : thetaP u u' hB (J2of Y u u' ν (toPts w)) w = K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    unfold thetaP
    rw [if_pos ⟨hJ, hP⟩, ← e, mul_div_cancel_left₀ _ hJ.ne']
  rw [e2]
  exact hW

def LocNormPK (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) * K = localAmplitudeProduct u u' hB w

theorem ooCorePK_of (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (hN : LocNormPK Y u u' C hB large₂ C1 νl) :
    OOCorePK Y u u' ν C hB large₂ C1 := by
  intro w hb hw
  rw [Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.hsNormSq_OOP_quot u u' ν νl hQ w hw (Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw)]
  exact hN w hb hw

end K

def LocalAmplitudeBounds {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocNormPK Y u u' C hB large₂ C1 νl) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)


def LocalAmplitudeBoundsUniform : Prop :=
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
      ∀ ν, Pinned X u u' ν → LocalAmplitudeBounds large₂ Y u u' ν C1 Cn Ire


end Formalism.L2.SG.Pf.OOCore3
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)
  (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))

def aT (τ : D.what₂.Tau) : ℂ := (((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ

def K0 : ℝ := (∏ τ, Complex.normSq (aT u u' C hB τ)) / Formalism.L2.SG.Pf.OOCore3.sclV Y u u'

def LocUniqP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) → ∀ τ,
      Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) =
        Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J ((νl w (vOf X τ)).map
          (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ)))) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ))

def MeasP : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau),
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) ((gamW X u u' w) (vOf X τ)) * Matrix.of x)))
      ((νl w (vOf X τ)).map (Formalism.L2.SG.Pf.LocJEq.Smap C τ ((gamW X u u' w) (vOf X τ))))

private theorem hsNormSq_real_smul' {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsNormSq (c • A) = Complex.normSq c * Formalism.MainNotions.S.hsNormSq A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← Finset.mul_sum]
  rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul]

theorem locNormPK_of (hU : LocUniqP u u' C hB νl) (hM : MeasP u u' C hB νl) (hK : 0 < K0 Y u u' C hB)
    (hW : Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (K0 Y u u' C hB)) : Formalism.L2.SG.Pf.OOCore3.LocNormPK Y u u' C hB large₂ C1 νl := by
  intro w hrow hrep
  refine ⟨K0 Y u u' C hB, hK, hW, ?_⟩
  have hs : Formalism.L2.SG.Pf.OOCore3.sclV Y u u' ≠ 0 := by
    intro h0
    unfold K0 at hK
    rw [h0, div_zero] at hK
    exact lt_irrefl _ hK
  have hfac : ∀ τ, Formalism.MainNotions.S.hsNormSq ((locS hB u u' τ).J (Formalism.L2.SG.Pf.JointAmplitudePoints.nu1P C u u' w τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ)) = Complex.normSq (aT u u' C hB τ) *
      Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Jv (νl w (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) ((gamW X u u' w) (vOf X τ))) := by
    intro τ
    rw [hU w hrow hrep τ]
    exact (congrArg Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.LocJEq.locJ_map_eq (C := C) (hB := hB) u u' τ _ _
      (hM w τ))).trans (hsNormSq_real_smul' _ _)
  unfold Formalism.L2.SG.Pf.JointAmplitudePoints.localAmplitudeProduct
  simp only [hfac, Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp X.pl.symm]
  unfold vOf K0
  field_simp

end Formalism.L2.SG.Pf.LocNorm
end
end
