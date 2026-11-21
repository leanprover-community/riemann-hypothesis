import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsLab
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import BuildAid.ForwardExisting

section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ (p : Point D.host.E (D.R.rS + 1)) (L U : GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D F0) F') = L * ptMat p * U → ∃ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) ≤ ENNReal.ofReal (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ^ (C * (D.R.rS : ℝ) ^ 2)) ∧ ∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ, ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∃ a : GramM D, (∀ j : Fin (D.R.rS + 1), n (frame F' j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame F' i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat p)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopC.CovTerm.covolume_term | exact GlobalTheory.LoopC.CovTerm.covolume_term | (intros; apply GlobalTheory.LoopC.CovTerm.covolume_term <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem leadMinorE_zhatL_dcrel :
    ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E)
      (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'),
      Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  intro D Λ T T' F F₁ F₂ h l
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := Formalism.L2.SG.Pf.zhat_rel F h
  rw [hZ]
  exact Formalism.L2.SG.Pf.leadMinor_uni A _ B hA0 hA1 hB0 hB1 l

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  atlas_forward_decl GlobalTheory.leadMinorE_zhatL_dcrel
end

section
section
noncomputable section

namespace GlobalTheory.LoopVol

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hhz_dcrel {D : D7} (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T') (h : Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂) (b C : ℝ) :
    Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₂) = Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₁) := by

  have hm : ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l :=
    GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset D Λ T T' F F₁ F₂ h
  simp only [Formalism.MainNotions.S.Cnt.HHZ, Formalism.MainNotions.S.Cnt.sizeZ, Formalism.MainNotions.S.Cnt.absDl, hm]

theorem volRC_le : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C, hC1, hcov⟩ := GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term Cg cb Cu cT CT C0 A
  refine ⟨C, ?_⟩
  intro D X Y hF hI W H Am hV large₂ u u' C' Cl hCl hHyp t hG hrel

  have hexp : (0 : ℝ) ≤ C * (D.R.rS : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hone : ∀ Z : Formalism.MainNotions.S.Cnt.GramM D,
      (1 : ℝ) ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C Z ^ (C * (D.R.rS : ℝ) ^ 2) := fun Z =>
    Real.one_le_rpow (Formalism.MainNotions.BridgeLemma₂.rows_one_le_HHZ D large₂ (by linarith) Z) hexp
  show Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C
    (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t)) ^ (C * (D.R.rS : ℝ) ^ 2)
  unfold Formalism.L2.SG.LoopTerm.volRC
  split_ifs with h
  swap
  · exact hone _
  have hs : h.2.2.choose.toTerm = tc hI t := h.2.2.choose_spec
  generalize h.2.2.choose = s at hs ⊢
  unfold Formalism.L2.SG.LoopTerm.covR
  split_ifs with hp
  swap
  · exact hone _
  have hat : s.toTerm.atPt hp.choose.1 := hp.choose_spec.1
  have hpin : Formalism.L2.SG.VolPin.IsPinnedR s hp.choose.1 hp.choose.2.1 := hp.choose_spec.2.1
  have hfund : Formalism.L2.SG.LoopTerm.IsFundR s hp.choose.2.2 := hp.choose_spec.2.2
  generalize hp.choose = x at hat hpin hfund ⊢
  obtain ⟨w, μR, K⟩ := x
  dsimp only at hat hpin hfund ⊢

  have htrel : (tc hI t).relevant := (hI.relevant t).1 hrel
  have hsrel : s.relevant := by
    show s.toTerm.relevant
    rw [hs]; exact htrel
  have hsG : s.G ≠ 0 := by
    show s.toTerm.G ≠ 0
    rw [hs, ← gterm_val hI t]
    exact (map_ne_zero _).2 hG

  have hP0 : Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u' s.frame := s.rep.2.2.2.2
  have hcls : s.toTerm.cls = Formalism.L2.SG.TermDef.mk _ _ _ ⟨s.frame, hP0⟩ := rfl
  have hEq := Formalism.L2.SG.TermTieOf.eqIff_base (Y := Y) (u' := u') s.lam s.mem
  obtain ⟨F₁, ⟨hP₁, hmk₁⟩, hG₁, hc₁⟩ := id hat
  have hR₁ : Formalism.L2.SG.TermDef.Rel s.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')
      ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ := (hEq _ _).1 (hmk₁.trans hcls)
  have hcb := (Formalism.L2.SG.TermTieOf.cellQ s.toTerm w ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ hR₁).1 ⟨hG₁, hc₁⟩

  have hlf := Formalism.L2.SG.TermTieOf.mapL_lf W u
  have hZ : ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) =
      ZhatL (lf D (X.Fu u)) s.frame := by
    rw [← hlf]; exact Formalism.L2.SG.Saturated.zhat_mapL _ _ _ _
  have hGv : Gval (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ≠ 0 := by
    rw [← hlf]
    exact (Formalism.L2.SG.Saturated.gval_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame).trans_ne hcb.1
  have hcell : IsInCell (ZhatOM (ZhatL (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame))) w := by
    rw [hZ]; exact hcb.2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  have hPm : Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) u'
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) s.frame).2 hP0

  obtain ⟨Ω, hΩ, hvol, hcv⟩ := hcov D large₂ u u' C' Cl hCl hHyp (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam)
    ⟨F0rec_e W u, F0rec_z_eq_zmOf W u⟩ (rowLat_rec H.lat s.lam s.mem)
    (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ⟨⟨hPm.1, hPm.2.1, hGv⟩, hPm.2.2⟩ w L U hL hU hLU
  have hμ := GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hHyp s hsrel hsG w μR K hat hpin hfund
    L U hL hU hLU Ω hΩ hcv
  have hle := hμ.trans hvol

  have hout : Formalism.L2.SG.TermDef.DCRel s.lam (lf D (X.Fu u)) (Quot.out s.toTerm.cls).1 s.frame :=
    (hEq (Quot.out s.toTerm.cls) ⟨s.frame, hP0⟩).1 ((Quot.out_eq _).trans hcls)
  have hdc : Formalism.L2.SG.TermDef.DCRel (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1)
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) _ _).2 hout
  have hfl : fl'Of W hI t = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1 := by
    rw [hs]; rfl
  rw [hfl, ← hhz_dcrel _ _ _ _ hdc large₂.sc.b C]
  exact ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one (hone _)) hle

end GlobalTheory.LoopVol

end
end

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  atlas_forward_decl GlobalTheory.LoopVol.volRC_le
end
