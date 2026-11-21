import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SideTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {b : Bool}
  {rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {S : RowSide D EE} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT}
  {jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)}

def ids (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowIds S (y.C F) b where
  jE := (LinearEquiv.ofInjective t.jE t.jE_inj).trans (LinearEquiv.ofEq _ _ t.jE_range)
  jM μ hμ j h1 h2 := (LinearEquiv.ofInjective (t.jM μ j) (t.jM_inj μ ((hU μ).1 hμ) j h1 h2)).trans
    (LinearEquiv.ofEq _ _ (t.jM_range μ ((hU μ).1 hμ) j h1 h2))
  jX μ hμ := (S.multTop μ).toLinearEquiv.trans ((LinearEquiv.ofInjective (t.jX μ) (t.jX_inj μ ((hU μ).1 hμ))).trans
    (LinearEquiv.ofEq _ _ (t.jX_range μ ((hU μ).1 hμ))))
  prt π := y.prtE F b (rep π)

theorem real (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowSideReal S (y.C F) b (ids hU t) bs ty where
  parY j hj := by
    show Mult.parB (Ptw D) (min j D.R.m) = Mult.parB (Ptw D) j
    rw [min_eq_left (by have := y.hm; omega)]
  lvl μ _ := GlobalTheory.HilbertLevels.eec_le_cc R F y.tupT y.hm y.hTop b μ
  lvlP μ _ j _ h2 := GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := y.hm; omega)
  lvlX μ _ := GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ
  ee x x' := t.jE_ip x x'
  mult μ hμ j h1 h2 x x' := t.jM_ip μ ((hU μ).1 hμ) j h1 h2 x x'
  multX _ μ hμ x x' := by
    rw [← (S.multTop μ).inner_map_map x x']
    exact t.jX_ip μ ((hU μ).1 hμ) _ _
  io0 _ μ hμ _ x v := by
    have hmem : t.jM μ 1 v ∈ (y.C F).CC b μ 1 :=
      GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := D.R.two_le_m; omega) ((ids hU t).jM μ hμ 1 le_rfl (by have := D.R.two_le_m; omega) v).2
    have e := t.io0 μ ((hU μ).1 hμ) x v hmem
    refine e.trans ?_
    rfl
  io0X h := absurd h (by have := D.R.two_le_m; omega)
  io μ hμ _ j h1 h2 x v := by
    have hmem : t.jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1) :=
      GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by omega) ((ids hU t).jM μ hμ (j + 1) (by omega) h2 v).2
    exact (t.io μ ((hU μ).1 hμ) j h1 h2 x v hmem).trans rfl
  ioTop h μ hμ _ x v := by
    have hmem : t.jX μ (S.multTop μ v) ∈ (y.C F).CCX b μ :=
      GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ ((ids hU t).jX μ hμ v).2
    exact (t.ioTop μ ((hU μ).1 hμ) x v _ (cast_heq _ _) hmem).trans rfl
  ft σ := by
    have h := t.ft (ty σ)
    have hs : bs σ ∈ Submodule.span ℂ (bs '' {σ' | ty σ' = ty σ}) := Submodule.subset_span ⟨σ, rfl, rfl⟩
    rw [h] at hs
    exact hs
  prt_disj π π' h := t.disj π π' h

end GlobalTheory.Mem.R3.Rw.SideTie

open GlobalTheory.Mem.R3.Rw.SideTie in

theorem GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y _ _ hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | exact GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | (intros; apply GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LiftRd

theorem liftTie_of_lfT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hI hB hU hLam rep jL t
  let I : LiftIds (y.L F) :=
    { jMj := fun i =>
        (LinearEquiv.ofInjective (t.jMj i) (t.jMj_inj i)).trans (LinearEquiv.ofEq _ _ (t.jMj_range i))
      jMt := fun μ hμ i =>
        (LinearEquiv.ofInjective (t.jMt μ i) (t.jMt_inj μ ((hU μ).1 hμ) i)).trans
          (LinearEquiv.ofEq _ _ (t.jMt_range μ ((hU μ).1 hμ) i))
      prtW := fun i π => y.prtW F i (rep π) }
  refine ⟨I, ⟨t.eW, t.eW_range, t.eW_norm, t.eW_lat⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
  refine ⟨fun i => GlobalTheory.HilbertLevels.holW R F y.tupT y.hm y.hTop y.hinj i, fun i x x' => t.jMj_ip i x x',
    fun μ hμ i x x' => t.jMt_ip μ ((hU μ).1 hμ) i x x', ?_, fun i π v => t.isot i π v,
    fun i π π' h => t.disj i π π' h, ?_⟩
  · intro μ hμ i x w _ hw hthC hgood
    exact t.theta μ ((hU μ).1 hμ) i x _ w hw hthC hgood
  · intro μ _ i π c h0 hc
    rw [hLam μ ((i : ℕ) + 1) (by omega) i.2 π h0]
    exact DV.lamTr_of_scalar D μ _ π c h0 hc

end GlobalTheory.Mem.R3.Rw.LiftRd

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftIdentifications_of_liftsComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.RepCls

theorem reps_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y Φ rep hR
  let f : Φ → principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0) :=
    fun π => Quotient.mk _ ⟨rep π, hR.mem π⟩
  have hinj : Function.Injective f := by
    intro π π' h
    exact hR.inj π π' (Quotient.exact h)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨π, hπ⟩ := hR.all (Formalism.L2.Col.finTypRep _ c) (Formalism.L2.Col.finTypRep_mem _ c)
    refine ⟨π, ?_⟩
    rw [← Quotient.out_eq c]
    exact Quotient.sound hπ
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun π => ?_⟩
  have hiso : (principalLevelFrame.rowRepR R.θ (Equiv.ofBijective f ⟨hinj, hsurj⟩ π)).Iso (rep π) :=
    Formalism.L2.Col.finTypRep_mk_iso ⟨rep π, hR.mem π⟩
  refine ⟨hiso, fun b => ?_, fun i => ?_, ?_⟩
  · unfold Hd.prtE principalLevelFrame.isotE
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hiso)]
  · unfold Hd.prtW
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ hiso]
  · obtain ⟨b, hb⟩ := hR.mem π
    refine ⟨b, ?_, ?_⟩
    · intro h
      apply hb
      unfold Hd.prtE at h
      rw [eq_bot_iff] at h ⊢
      intro x hx
      have h0 := h (Submodule.mem_map_of_mem hx)
      rw [Submodule.mem_bot] at h0 ⊢
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · exact Submodule.map_mono inf_le_left

end GlobalTheory.Mem.R3.Rw.RepCls
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_identification_typeRepresentatives_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  first | exact @GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | exact GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | (intros; apply GlobalTheory.Mem.R3.Rw.RepCls.reps_classes <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.ComplexificationCasts

theorem heq_funCongr {K : Type} [Field K] {a b : ℕ} (h : b = a) (x : Fin a → K) :
    HEq (LinearEquiv.funCongrLeft K K (finCongr h) x) x := by
  subst h; rfl

theorem complexificationCastCoords_j_eq_comp_funCongrLeft {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    (t.cast h).j = t.j.comp (LinearEquiv.funCongrLeft K K (finCongr (congrArg Mat1.n h))).toLinearMap := by
  subst h; rfl

theorem cast_forms {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    FormsTie σ (t.j.comp (LinearEquiv.funCongrLeft K K (finCongr (congrArg Mat1.n h))).toLinearMap) m'.H m'.E s.e :=
  complexificationCastCoords_j_eq_comp_funCongrLeft h t ▸ (t.cast h).forms

theorem cast_lat {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    OLatTie σ s.lat (t.j.comp (LinearEquiv.funCongrLeft K K (finCongr (congrArg Mat1.n h))).toLinearMap) m'.N :=
  complexificationCastCoords_j_eq_comp_funCongrLeft h t ▸ (t.cast h).latT

theorem cast_apply {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) (x) :
    t.j (LinearEquiv.funCongrLeft K K (finCongr (congrArg Mat1.n h)) x) = (t.cast h).j x := by
  subst h; rfl

theorem cen_of_tie {K : Type} [Field K] [NumberField K] [StarRing K] {G H : Type} [Group G] [Group H] {O : Type} [CommRing O]
    {φ : O →+* ℂ} {σ : K →+* ℂ} {m : Mat1 K G} {s : Sp1 O φ G} (t : Tie1 σ m s) (e : G ≃* H)
    (c : Subalgebra.center ℂ (MonoidAlgebra ℂ H) → s.A.T → s.A.T)
    (hc : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)),
      (∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g)) → ∀ x, c z x = s.act z' x)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (a : MonoidAlgebra K G)
    (ha : ∀ g, σ (a.coeff g) = (z : MonoidAlgebra ℂ H).coeff (e g)) (x : Fin m.n → K) :
    c z (t.j x) = t.j ((m.op a).mulVec x) :=
  (hc z (Bare.cenPull e z) (Bare.coeff_cenPull e z) _).trans
    (t.cen _ a (fun g => (ha g).trans (Bare.coeff_cenPull e z g).symm) x)

theorem stdIso_of_keep {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B}
    {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) (cG)
    (hk : Keep (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) z.R.toRealDat z.F.lv2 cG) : StdIso X px (z.R.eG.trans cG) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := hk.grp
  have hP : z.R.Pg = (X.B.primes px).vGs := z.lev.Pg
  refine ⟨plg.trans (Equiv.subtypeEquivRight fun x => by rw [hP]; exact Iff.rfl), iso, h1, fun g kv => ?_⟩
  exact (z.idG g (plg kv).1 _ (plg kv).2).symm.trans (h4 g kv)

theorem iota_eq_zero {R : Ranks} (D : Rows.Data R) (hm : 0 < R.m) (μ : D.Tup) (h : ∀ j, D.io μ j = 0) : D.iota μ = 0 := by
  have : ∀ k, 0 < k → D.downTo μ k = 0 := fun k hk => by
    cases k with
    | zero => omega
    | succ k => rw [Rows.Data.downTo, h, LinearMap.comp_zero]
  rw [Rows.Data.iota, this _ hm, LinearMap.zero_comp, LinearMap.comp_zero]

theorem bu_word (D : D7) (h : Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (hK : ∀ φ F, F ∈ D.what₂.V0 D.what₂.mu0 → D.what₂.iota D.what₂.mu0 F = 0 → D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (φ F) (hF : F ∈ D.what₂.V0 D.what₂.mu0) : D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK φ n hnU.1 hnU.2, add_zero]

theorem exists_type {E A Φ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [AddCommGroup A] [Module ℂ A] {n : ℕ}
    (bs : Fin n → E) (ty : Fin n → Φ) (π : Φ) (j : E →ₗ[ℂ] A) (P : Submodule ℂ A)
    (h : Submodule.span ℂ (bs '' {σ | ty σ = π}) = P.comap j) (h0 : P ≠ ⊥) (hle : P ≤ LinearMap.range j) : ∃ σ, ty σ = π := by
  by_contra hn
  have he : {σ | ty σ = π} = ∅ := Set.eq_empty_of_forall_notMem fun σ hσ => hn ⟨σ, hσ⟩
  rw [he, Set.image_empty, Submodule.span_empty] at h
  refine h0 (eq_bot_iff.2 fun v hv => ?_)
  obtain ⟨x, rfl⟩ := hle hv
  have hx : x ∈ P.comap j := hv
  rw [← h, Submodule.mem_bot] at hx
  rw [hx, map_zero]; exact Submodule.zero_mem _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem xi_base (hB : R.BaseW F) : R.toLevCh.xi A.μ0 = 1 := by
  have h := hB.lev.xi A.μ0
  rw [hB.lev.xi_base] at h
  exact MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq h)

theorem colTie (y : Hd R) (hB : R.BaseW F) (hb : Rows.BuDefQ D.what₂) :
    ColTieR (y.C F) ⟨fun μ => R.toLevCh.xi (y.tupT μ)⟩ := by
  have h0 : R.toLevCh.xi (y.tupT D.what₂.mu0) = 1 := by rw [← y.tup0, y.tupT_tup]; exact xi_base hB
  refine ⟨fun μ _ j _ _ => ?_, h0, bu_word D hb⟩
  show R.toLevCh.mu0 j * R.toLevCh.xi (y.tupT μ) = R.toLevCh.mu0 j * R.toLevCh.xi (y.tupT D.what₂.mu0) * R.toLevCh.xi (y.tupT μ)
  rw [h0, mul_one]

theorem exists_eE (y : Hd R) (hB : R.BaseW F) (b : Bool) {E : Type} [AddCommGroup E] [Module ℂ E] (j : E →ₗ[ℂ] (y.C F).Amb 0)
    (hj : LinearMap.range j = (y.C F).EEc b) :
    ∃ e : E →ₗ[ℂ] R.HE.H, ∀ x, j x = PiTensorProduct.lift (R.HE.e (e x)) := by
  have hE : R.models_HE := hB.models.HE
  let k : R.HE.H →ₗ[ℂ] (y.C F).Amb 0 := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap ∘ₗ R.HE.e
  have hk : Function.Injective k := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective.comp hE.1
  have hr : ∀ x, j x ∈ LinearMap.range k := fun x => by
    have h1 : j x ∈ (y.C F).EEc b := hj ▸ LinearMap.mem_range_self j x
    obtain ⟨U, hU, hx⟩ := h1
    obtain ⟨v, hv⟩ := hE.2.1.ge (GlobalTheory.GoodRowsLevel.eeat_le_triv R (R.levR F b) hU)
    exact ⟨v, (congrArg (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) hv).trans hx⟩
  refine ⟨(LinearEquiv.ofInjective k hk).symm.toLinearMap ∘ₗ j.codRestrict _ hr, fun x => ?_⟩
  exact (congrArg Subtype.val ((LinearEquiv.ofInjective k hk).apply_symm_apply ⟨j x, hr x⟩)).symm

theorem tupTie (y : Hd R) {μ} (h : y.Us μ) : y.tup (y.tupT μ) = μ := by
  rcases h with h | ⟨w, h⟩
  · rw [h, ← y.tup0, y.tupT_tup]
  · rw [h, y.tupT_tup]

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

theorem muAt_eq (m : Moved o) (v) : (w.st o.Z).toD7.what₂.muAt v = m.y.tup (m.z.R.mu ((w.st o.Z).toD7.plEq v)) := by
  rw [m.tup]
  refine w.ok.xi_inj (Eq.trans ?_ (m.z.mu v).2.symm)
  by_cases h : v ∈ Wt
  · exact ((congrArg w.I.xi (q.mu.on v h)).trans ((q.mu.tw v).trans (congrArg (fun c => T.xiTw c v) w.C_eq.symm))).trans
      (if_pos h).symm
  · exact ((congrArg w.I.xi (q.mu.off v h)).trans w.l.xi0).trans (if_neg h).symm

end GlobalTheory.Mem.R3.Rw.ComplexificationCasts

set_option maxHeartbeats 4000000 in
open GlobalTheory.Mem.R3.Rw.ComplexificationCasts in

theorem GlobalTheory.Mem.R3.Rw.read_of_moved : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∀ s : Side0 o, ∃ Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0, Y.tup = m.y.tup ∧ Y.tupT = m.y.tupT ∧ Y.PY = m.y.PY ∧ Y.PW = m.y.PW ∧ (∀ t, HEq (Y.jA t) ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j) ∧ (∀ t, HEq (Y.jA0 t) ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j) ∧ (∀ (i : Fin (w.D o.Z).R.m) t x, HEq (Y.eMt i t x) x) ∧ (∀ π, (principalLevelFrame.rowRepR m.z.R.θ (Y.eFT π)).Iso (m.t.rep π)) ∧ (∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) ∧ (∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) ∧ (∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) ∧ (∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)) := by
  intro B f T w Z₀ hX Wt z₀ q o hin hfits m s
  have hB : m.z.R.toRealDat.BaseW m.z.F.lv2 := m.z.pins.char.base
  have hmu := muAt_eq m
  have hU : ∀ μ, Used0 (w.st o.Z).toD7 μ ↔ m.y.Us μ := by
    intro μ; unfold Used0 Hd.Us; simp only [hmu]
  have hN : NumOK (w.st o.Z).toD7 := q.num o.η o.hη o.V o.S o.N o.G
  have k1 := GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y hin hB hU true m.t.rep _ (RowSide.sharp (w.st o.Z).toD7) _
    (w.st o.Z).toD7.what₂.onb (w.st o.Z).toD7.what₂.ft (fun t x => ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j x) (m.t.ch true)
  obtain ⟨Ish, h1R, h1P, h1E, h1X⟩ := k1
  have k0 := GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y hin hB hU false m.t.rep _ s.p0.s _
    (w.st o.Z).toD7.what₂.onb0 (w.st o.Z).toD7.what₂.ft0 (fun t x => ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j x) (m.t.ch false)
  obtain ⟨Iz, h0R, h0P, h0E, h0X⟩ := k0
  have kL := GlobalTheory.T.liftIdentifications_of_liftsComparison _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y hin hB hU hN.lam m.t.rep _ m.t.lf
  obtain ⟨IL, mj, hLT, hPW, hMj, hMt, hEW⟩ := kL
  have kF := GlobalTheory.T.exists_identification_typeRepresentatives_classes _ _ _ _ _ _ m.z.R.toRealDat m.z.F.lv2 m.y _ m.t.rep m.t.reps
  obtain ⟨eF, heF⟩ := kF
  have kE := exists_eE m.y hB true (m.t.ch true).jE (m.t.ch true).jE_range
  obtain ⟨eE, heE⟩ := kE
  have hocc : ∀ π, (∃ σ, (q.p.ch true).ty σ = π) ∨ ∃ σ, (q.p.ch false).ty σ = π := fun π => by
    have k := (heF π).2.2.2
    obtain ⟨b, h0, hle⟩ := k
    have k' := exists_type (q.p.ch b).bs (q.p.ch b).ty π (m.t.ch b).jE _ ((m.t.ch b).ft π) h0 (hle.trans (m.t.ch b).jE_range.ge)
    cases b
    · exact Or.inr k'
    · exact Or.inl k'
  refine ⟨{
    tup := m.y.tup
    tupT := m.y.tupT
    tupT_tup := m.y.tupT_tup
    tupTie := fun μ h => tupTie m.y ((hU μ).1 h)
    tup0 := m.y.tup0
    muAt := hmu
    hm := m.y.hm
    hTop := m.y.hTop
    hinj := m.y.hinj
    Ish := Ish
    Iz := Iz
    IL := IL
    Kc := ⟨fun μ => m.z.R.toLevCh.xi (m.y.tupT μ)⟩
    PY := m.y.PY
    PW := m.y.PW
    eFT := eF
    ιW := m.y.ιW
    tied := ⟨h1R, h0R, hLT, colTie m.y hB hN.bu⟩
    prtE := fun π => by kexactB (h1P π).trans ((heF π).2.1 true).symm
    prtE0 := fun π => by kexactB (h0P π).trans ((heF π).2.1 false).symm
    prtWE := fun i π => by kexactB (hPW i π).trans ((heF π).2.2.1 i).symm
    xi := fun _ _ => rfl
    isomFin := m.y.isomFin
    frameMatch := m.y.frameMatch
    hF := m.y.hF
    stdPsi := m.y.stdPsi
    jA := fun t => by kexactB ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).j
    jA0 := fun t => by kexactB ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).j
    eMt := fun i t => by kexactB (LinearEquiv.funCongrLeft B.LL B.LL (finCongr (congrArg Mat1.n (m.t.hL i t))))
    formsA := fun t => by kexactB ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).forms
    latA := fun t => by kexactB ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)).latT
    formsAtBottomLevel := fun t => by kexactB ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).forms
    latA0 := fun t => by kexactB ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)).latT
    formsL := fun i t => by kexactB (cast_forms (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)))
    latL := fun i t => by kexactB (cast_lat (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)))
    topRead := fun t h x => by
      kexactB ((h1X _ h _).trans ((congrArg ((m.t.ch true).jX (m.y.tup t))
        (((q.p.ch true).multTop (m.y.tup t)).apply_symm_apply _)).trans ((m.t.ch true).top t ((hU _).1 h) x)))
    topRead0 := fun t h x => by
      kexactB ((h0X _ h _).trans ((congrArg ((m.t.ch false).jX (m.y.tup t))
        (((q.p.ch false).multTop (m.y.tup t)).apply_symm_apply _)).trans ((m.t.ch false).top t ((hU _).1 h) x)))
    mtRead := fun i t h x => by
      kexactB ((hMt _ h i _).trans ((congrArg (m.t.lf.jMt (m.y.tup t) i)
        (cast_apply (m.t.hL i t) (q.p.tL (m.y.tup t) ((i : ℕ) + 1)) x)).trans (m.t.lf.read i t ((hU _).1 h) x)))
    mj := mj
    mjRead := fun i v => by
      kexactB ((hMj i v).trans ((m.t.lf.jMj_read i v).trans
        (congrArg (fun u => PiTensorProduct.lift ((m.z.R.HW i _).e u)) (hEW i v).symm)))
    stable := fun μ => by kexactB (m.t.tA true μ).stable
    stable0 := fun μ => by kexactB (m.t.tA false μ).stable
    eE := by kexactB eE
    eE_read := fun x => by kexactB ((h1E x).trans (heE x))
    dall := by kexactB m.t.dall
    junk := fun μ h => iota_eq_zero _ m.y.hm μ ((m.t.ch true).junk μ fun h' => h ((hU μ).2 h'))
    cen0 := fun cG hk t => by
      kexactB (cen_of_tie ((m.t.tA false (m.y.tup t)).cast (m.t.hA false t)) (m.z.R.eG.trans cG) (fun z x => s.cen (m.y.tup t) z x)
        (s.is _ (stdIso_of_keep m.z cG hk) (m.y.tup t)))
    cen1 := fun cG hk t => by
      kexactB (cen_of_tie ((m.t.tA true (m.y.tup t)).cast (m.t.hA true t)) (m.z.R.eG.trans cG)
        (fun z x => o.N.ntypes.cenAmb (m.y.tup t) z x) ((hfits.cen _ (stdIso_of_keep m.z cG hk)).amb (m.y.tup t)))
    lam := hN.lam
    occ := by kexactB hocc
    kap := q.kap o.η o.hη o.V o.S o.N o.G
    bu := hN.bu
    ze := hN.ze }, rfl, rfl, rfl, rfl, fun t => HEq.rfl, fun t => HEq.rfl, fun i t x => ?_, fun π => (heF π).1,
    fun x => heq_of_eq (h1E x), fun x => heq_of_eq (h0E x), fun i x => heq_of_eq (hEW i x), fun μ h i x => heq_of_eq (hMt μ h i x)⟩
  kexactB (heq_funCongr (K := B.LL) (congrArg Mat1.n (m.t.hL i t)) x)

end
end
