import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.NoBoundaryComponentOfAbelianAtGenericPoints
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutDivD
import Formalism.SharpRestriction.Divisibility.ChainOperators.CutKapD
import Formalism.SharpRestriction.Divisibility.ChainOperators.RankInputBounds
import Formalism.SharpRestriction.Divisibility.ChainOperators.GeometricGenericity
import Formalism.SharpRestriction.Divisibility.IsotypicCorollary

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section P18rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)















theorem division_admissible_of_inputs (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ)
    (h8 : ThetaNormsAndLinks.Conclusion₂ D L X H C2 A2 CR CT CRd) (h66 : ModuliIntegralCharts.LinkConditions D X.P6) (h08 : WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT)
    (a7 : LiftErrorLocal.adm7 D X) (a8 : LiftErrorLocal.adm8 D X) (a9 : LiftErrorLocal.adm9 D X) (a12 : LiftErrorLocal.adm12 D) :
    LiftErrorLocal.admitted D L X H C2 A2 CR CT CRd := by
  obtain ⟨p1, p2, p3b, p5, p6, p6b, -, p10, p11, -⟩ := h8
  exact ⟨p1, p2, h66, p3b, h08, p5, p6, p6b, a7, a8, a9, p10, p11, a12⟩



end P18rec

section PDV08rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : ThetaNormsAndLinks.Loc8 X)






def ThetaNormLinkHypotheses (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  ThetaNormsAndLinks.admissible_unitary_of_inputs D X Z ∧ ThetaNormsAndLinks.SandwichExists D X ∧ ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd ∧ ThetaNormsAndLinks.MirabolicIndexCond D ∧
    (ThetaNormsAndLinks.admR D nch ∧ ThetaNormsAndLinks.admG2 D ∧ ThetaNormsAndLinks.BadRowShareBound D L nch ∧ ThetaNormsAndLinks.EqualGoodMultiplicities D nch ∧ ThetaNormsAndLinks.SupLatticeGroupStable D) ∧ ThetaNormsAndLinks.SupSpansPsiPart D ∧
    (ThetaNormsAndLinks.AdditiveCharacterIntegrality D X ∧ ThetaNormsAndLinks.ScalingIntegrality D X ∧ ThetaNormsAndLinks.CrudeIntegrality D X ∧ ThetaNormsAndLinks.ThetaLevelPrimeIntegrality D X) ∧
    (ThetaNormsAndLinks.admT4 D X ∧ ThetaNormsAndLinks.NormDecompositionCond D X Z ∧ ThetaNormsAndLinks.ThetaKGroupStable D X Z ∧ ThetaNormsAndLinks.ThetaKEquivariantData D X Z ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D X) ∧
    (ThetaNormsAndLinks.RunColumnChoices D X ∧ ThetaNormsAndLinks.ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ ThetaNormsAndLinks.FurtherSizeConditions D L X H C2 A2 CR ∧ ThetaNormsAndLinks.GlobalScalarBounds D L X H ∧
      ThetaNormsAndLinks.RegularityOffTypePrimes D L X H)


theorem inputs_admissible_of (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) (hM : WeightFamilies.adm1 X.B)
    (hB : WeightFamilies.TransferenceTheoremCond) (lv : ThetaNormLinkHypotheses D L X Z H C2 A2 CR CT CRd) : ThetaNormsAndLinks.admitted D L X Z H C2 A2 CR CT CRd := by
  obtain ⟨aI, aQ, aRk, aG, ⟨aR, aG2, aBad, aTR, aGst⟩, aSp, aS, ⟨aT4, aNN, aK, aD, aW⟩, aRun⟩ := lv
  exact ⟨aI, aQ, hB, aRk, aG, ⟨aR, aG2, aBad, aTR, CutDivD.projector_statement_of_stability D aGst, aGst⟩, aSp, aS, ⟨hM, aT4, aNN, aK, aD, aW⟩, aRun⟩

end PDV08rec


section P18parts

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def UnitClauseAtBaseTuple : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1 ≤ LiftErrorLocal.twistV0Submodule D nch w j b ∧
    (D.what₂.Ij D.what₂.muStar j (LiftErrorLocal.plS nch w b) : ℝ) ≤ (D.what₂.places.ramIdx (LiftErrorLocal.plS nch w b) : ℝ) * X.IsgBase w j b

def TwistedIndexBound (D : D7) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, TwistedAt D w →
  (D.what₂.jw (D.what₂.muTw w) j w : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

theorem unit_clause_admissible_of_parts (hb : UnitClauseAtBaseTuple X) (hU : ∀ w, TwistedAt D w → PDVN.UAt X w) (hjw : TwistedIndexBound D) : LiftErrorLocal.adm7 D X :=
  fun i0 w hw j hj => ⟨hb i0 w hw j hj, fun ht => ⟨hU w ht j hj, hjw i0 w hw j hj ht⟩⟩

theorem twist_admissible_of_good_twists' (h : TwGoodAt D nch X.I) : LiftErrorLocal.adm8 D X := fun _ w _ hw => h w hw

end P18parts

structure Trip (D : D7) where
  B : WeightFamilies.Prov D
  P : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P

def tripOf {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) : Trip D := ⟨X.B, X.P6, X.W⟩

section Fam

variable {eps : ℝ} (Fm : FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)

theorem theorem_zero_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR : ℝ)
    (h : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (XF x hx i) H C2h A2 CR (Fm.Ct + 1) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx h0 i => h x hx h0 i⟩

theorem jet_admissible_family_of
    (h : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.adm3 (Fm.D x i) (XF x hx i) := h

theorem division_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (h8 : ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (h66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6)
    (h08 : WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
      (fun x hx i => (XF x hx i).W) H C2h A2 CR)
    (unit_twist_local_clauses_family : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i)) :
    LiftErrorLocal.AdmF Fm XF H C2h A2 CR CRd := by
  obtain ⟨xa, h8⟩ := h8
  obtain ⟨xb, h08⟩ := theorem_zero_admissible_family_of Fm XF H C2h A2 CR h08
  obtain ⟨xc, unit_twist_local_clauses_family⟩ := unit_twist_local_clauses_family
  refine ⟨max xa (max xb xc), fun x hx h0 i => ?_⟩
  have ha : xa ≤ x := le_trans (le_max_left _ _) h0
  have hb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hc : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨a7, a8, a9, a12⟩ := unit_twist_local_clauses_family x hx hc i
  exact division_admissible_of_inputs _ _ _ H C2h A2 CR _ CRd (h8 x hx ha i) (jet_admissible_family_of Fm XF h66 x hx i) (h08 x hx hb i) a7 a8 a9 a12

variable (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))

theorem inputs_admissible_family_of (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ)
    (hM : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)) (hB : WeightFamilies.TransferenceTheoremCond)
    (lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd) :
    ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd := by
  obtain ⟨x0, lv⟩ := lv
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have h1 : WeightFamilies.adm1 (XF x hx i).B := hM x hx i
  exact inputs_admissible_of _ _ _ _ H C2h A2 CR _ CRd h1 hB (lv x hx h0 i)

end Fam

section ChainF

variable {eps : ℝ} (Fm : FamP eps)

theorem chain_sup_lattice_family (T : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Trip (Fm.D x i)) (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass)
    (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (Ch Ah Cq Aq C2h A2 CR CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (ob : ∀ x hx i, Ob (Fm.L x i) (T x hx i).B)
    (o8 : ∀ x hx i, O8 (Fm.L x i) (T x hx i).B (T x hx i).P (T x hx i).W)
    (a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, WeightAlgebra.adm1 (T x hx i).B ∧
      WeightAlgebra.adm2 (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧ WeightAlgebra.adm3 (Fm.L x i) (T x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (T x hx i).W H.CA H.C1 H.A1 K.CW K.AW)
    (b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (T x hx i).B)) (b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (T x hx i).B))
    (bB : WeightFamilies.TransferenceTheoremCond) (bC : WeightFamilies.ChowlaSelbergFamily Fm) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) H C2h A2 CR := by
  obtain ⟨x0, a14⟩ := a14
  obtain ⟨⟨x1, p1⟩, p2, ⟨x3, p3⟩⟩ := s08b (fun x hx i => (T x hx i).B) ob
    ⟨b1, ⟨x0, fun x hr hx i => (a14 x hr hx i).2.1.2⟩, b3, bB, bC⟩
  refine s08 (fun x hx i => (T x hx i).B) (fun x hx i => (T x hx i).P) (fun x hx i => (T x hx i).W) o8
    ⟨max x0 (max x1 x3), fun x hr hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨a1, a2, a3, a4⟩ := a14 x hr hx0 i
  exact ⟨a1, a2, a3, a4, p1 x hr hx1 i, p2 x hr i, p3 x hr hx3 i⟩

variable (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
  (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6))

structure LvG (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (C2h A2 CR CRd : ℝ) : Prop where
  ob : ∀ x hx i, Ob (Fm.L x i) (XF x hx i).B
  o8 : ∀ x hx i, O8 (Fm.L x i) (XF x hx i).B (XF x hx i).P6 (XF x hx i).W
  o18 : ∀ x hx i, O18 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)
  a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      WeightAlgebra.adm2 (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧
      WeightAlgebra.adm3 (Fm.L x i) (XF x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CW K.AW
  b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)
  b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (XF x hx i).B)
  bB : WeightFamilies.TransferenceTheoremCond
  bC : WeightFamilies.ChowlaSelbergFamily Fm
  a66 : BoundaryLocalData.AdmFx Fm (fun x hx i => (XF x hx i).P6) YF
  lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd
  a79 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      UnitClauseAtBaseTuple (XF x hx i) ∧ TwistedIndexBound (Fm.D x i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)
  aU : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∀ w, TwistedAt (Fm.D x i) w → PDVN.UAt (XF x hx i) w
  aTG : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (XF x hx i).I
  a12 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, N.LocsCoverTw (Fm.D x i)

theorem LvG.unit_twist_local_clauses_family {Ob : WeightFamilies.ObjClass} {O8 : WeightAlgebra.ObjClass} {O18 : LiftErrorLocal.ObjClass} {K : WeightAlgebra.KAdm} {H : WeightAlgebra.KHyp} {C2h A2 CR CRd : ℝ}
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.adm7 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm8 (Fm.D x i) (XF x hx i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i) ∧
        LiftErrorLocal.adm12 (Fm.D x i) := by
  obtain ⟨a, h1⟩ := lv.a79
  obtain ⟨b, h2⟩ := lv.aU
  obtain ⟨c, h3⟩ := lv.aTG
  obtain ⟨d, h4⟩ := lv.a12
  refine ⟨max (max a b) (max c d), fun x hx h0 i => ?_⟩
  have ha : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h0
  have hb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h0
  have hc : c ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have hd : d ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨b7, j7, h9⟩ := h1 x hx ha i
  exact ⟨unit_clause_admissible_of_parts _ b7 (h2 x hx hb i) j7, twist_admissible_of_good_twists' _ (h3 x hx hc i), h9, h4 x hx hd i⟩

theorem chainGF (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (Ch Ah Cq Aq C2h A2 CR ka CRd C1 C2 C3 CA CD CH : ℝ)
    (s08b : WeightFamilies.PacketAlongFamilyInClass Ob K.CG K.AG K.CL K.AL K.CRm H.CK Ch Ah Cq Aq Fm CH)
    (s08 : WeightAlgebra.PeriodFamilyStatement O8 K H Ch Ah Cq Aq C2h A2 CR Fm CH)
    (s66b : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (XF x hx i).P6) YF ka)
    (sIn : ThetaNormsAndLinks.AdmF Fm XF ZF H C2h A2 CR CRd → ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd)
    (s18 : LiftErrorLocal.KudlaFamilyStatement O18 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH)
    (lv : LvG Fm XF ZF YF Ob O8 O18 K H C2h A2 CR CRd) :
    WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
                  (fun x hx i => (XF x hx i).W) H C2h A2 CR ∧
      ThetaNormsAndLinks.ConclusionOnFamily Fm XF H C2h A2 CR CRd ∧ LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD := by
  have p08 := chain_sup_lattice_family Fm (fun x hx i => tripOf (XF x hx i)) Ob O8 K H Ch Ah Cq Aq C2h A2 CR CH s08b s08 lv.ob lv.o8 (lv.a14.imp fun _ h x hx h0 i => ⟨lv.b1 x hx i, h x hx h0 i⟩) lv.b1
    lv.b3 lv.bB lv.bC
  have p66 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P6 :=
    fun x hx i => (s66b lv.a66 x hx i).2.2.2.2
  have pIn := sIn (inputs_admissible_family_of Fm XF ZF H C2h A2 CR CRd lv.b1 lv.bB lv.lv)
  exact ⟨p08, pIn, s18 XF lv.o18 (division_admissible_family_of Fm XF H C2h A2 CR CRd pIn p66 p08 lv.unit_twist_local_clauses_family)⟩



end ChainF

abbrev gK (sb : WeightFamilies.Sel) (K0 : WeightAlgebra.KAdm) : WeightAlgebra.KAdm := { K0 with CL := sb.C K0.CG K0.AG, AL := sb.A K0.CG K0.AG }

abbrev gCq (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  sb.Cc K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg)

abbrev gAq (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  sb.Ac K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg)

abbrev rankConstantOfSelection (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.C2 (gK sb K0) H (gCq sb s8 K0 H) (gAq sb s8 K0 H)

abbrev rankExponentOfSelection (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.A2 (gK sb K0).deg H.deg (gAq sb s8 K0 H)

abbrev gCR (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) : ℝ :=
  s8.CR (gK sb K0).deg H.deg (gAq sb s8 K0 H)

theorem chainG (𝒞 : FamClass) (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (ka : ℝ)
    (h08b : WeightFamilies.ClosedAbsoluteShare Ob 𝒞) (h08 : WeightAlgebra.ClosedSupNormFirstForm O8 𝒞) (h66 : BoundaryLocalData.ClosedFamilyKeyFormula 𝒞 ka)
    (hIn : ThetaNormsAndLinks.ClosedAbsoluteShare 𝒞)
    (h18 : LiftErrorLocal.ClosedAbsoluteShare O18 𝒞) :
    ∃ (sb : WeightFamilies.Sel) (s8 : WeightAlgebra.Sel) (C1 C2 C3 CA CD : ℝ), Closed 𝒞 fun Fm _ =>
      ∀ (K0 : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp) (CRd : ℝ), 2 ≤ K0.CRm → 2 ≤ CRd →
      ∀ (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
        (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
        (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6)),
        LvG Fm XF ZF YF Ob O8 O18 (gK sb K0) H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) CRd →
        WeightAlgebra.ConclusionF1 Fm (fun x hx i => (XF x hx i).B) (fun x hx i => (XF x hx i).P6)
                      (fun x hx i => (XF x hx i).W) H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) ∧
          ThetaNormsAndLinks.ConclusionOnFamily Fm XF H (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) CRd ∧
          LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD := by
  obtain ⟨sb, h08b⟩ := h08b
  obtain ⟨s8, h08⟩ := h08
  obtain ⟨C1, C2, C3, CA, CD, h18⟩ := h18
  refine ⟨sb, s8, C1, C2, C3, CA, CD, (h08b.and (h08.and (h66.and (hIn.and h18)))).imp
    fun Fm CH _ h K0 H CRd hCRm hCRd XF ZF YF lv => ?_⟩
  obtain ⟨a, b, e, c, d⟩ := h
  exact chainGF Fm XF ZF YF Ob O8 O18 (gK sb K0) H (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg) (gCq sb s8 K0 H)
    (gAq sb s8 K0 H) (rankConstantOfSelection sb s8 K0 H) (rankExponentOfSelection sb s8 K0 H) (gCR sb s8 K0 H) ka CRd C1 C2 C3 CA CD CH
    (a K0.CG K0.AG K0.CRm H.CK (s8.Ch (gK sb K0) H) (s8.Ah (gK sb K0).deg H.deg))
    (b (gK sb K0) H (gCq sb s8 K0 H) (gAq sb s8 K0 H) hCRm) (e _ YF) (c H _ _ _ CRd hCRd XF ZF) (d H _ _ _ CRd hCRd) lv

section ON

variable {D : D7} {CH : NChoice D} {Xd : DivX D}





def ONIn (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 CA : ℝ) : Prop :=
  (WeightAlgebra.Conclusion1 L O.X.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X CRd ∧ ThetaNormsAndLinks.RunConditions D L O.X H C2 A2 CR CT CRd) ∧
  (WeightAlgebra.Conclusion1 L O.X'.W H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D O.X' CRd ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D O.X' ∧ ThetaNormsAndLinks.RunConditions D L O.X' H C2 A2 CR CT CRd) ∧
  (LiftErrorLocal.ConjugationNormInvariance D L O.X CA ∧ ThetaNormsAndLinks.LinkConditions D O.X) ∧
  (ThetaNormsAndLinks.AtEveryPlace D O.X ∧ ThetaNormsAndLinks.LinkLatticesEveryPlace D O.X') ∧
  (CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6)

def ONLv (L : SizeData₂ D) (O : PDVN.ONObj D CH Xd) (C6 Cd Cs : ℝ) : Prop :=
  L.FDef ∧ PDVN.unitBoundAtTwistedPlaces O ∧ PDVN.DepthFromContent L O C6 Cd ∧ PDVN.TypePrimeSizeConds L O Cs ∧ PDVN.TwistedPlacesCover D



end ON

section ONF

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)



end ONF

section ONchain

variable {eps : ℝ} (Fm : FamP eps)


variable (OF : PDVN.ONObjF Fm)


end ONchain

section ONstmts

variable {eps : ℝ} (Fm : FamP eps) (OF : PDVN.ONObjF Fm)


end ONstmts

end Formalism.MainNotions.DIV

end
