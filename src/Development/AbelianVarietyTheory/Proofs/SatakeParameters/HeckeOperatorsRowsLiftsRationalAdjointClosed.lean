import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement

section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHeckeCore

open Formalism.DivisionValues Formalism.IndefR Formalism.L2.Theta GlobalTheory.HeckeRational GlobalTheory.SplitHeckeAdj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (t i a b) :
    (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degR t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k D.sp.X'.rank with hk' | hk'
  · exact rows_dcOp_mem_cmMax R hf.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degR t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem lifts_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (j t i a b) :
    (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degL j t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k (Vc D j).rank with hk' | hk'
  · exact lifts_dcOp_mem_cmMax R hf.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degL j t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem hecke_okH_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (_F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, (A.fam.R t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.R t).op) ∧ ∀ j t, (A.fam.L j t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.L j t).op := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ hl hf hm
  obtain ⟨gramR, c0R, c0L, tie⟩ := hf.tie
  have honto : ∀ t PP, Bridge.SplitOff PP ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) → ∃ P, R.pl P = PP :=
    fun t PP hP => hf.pl_onto PP (splitOff_mono Set.subset_union_left hP)
  have hS : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
    fun t PP hP => hP.elim (fun h1 => Or.inl (hf.Sb h1)) Or.inr
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · obtain ⟨c, hc⟩ := hl.βX
    rw [one_pow] at hc
    have h := side_adj_comm D.sp.X' R.βX R.ΛX (R.datXt t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      R.cX.coef.ρ (fun γ => hm.cX.2.1 γ) D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres (A.heckeR t)
      (R.B.R t).hecke (hf.degR t)
    exact ⟨⟨rows_opMat_mem R hf t, h.1⟩, h.2⟩
  · obtain ⟨c, hc⟩ := hl.βV j
    rw [one_pow] at hc
    have h := side_adj_comm (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      (R.cV j).coef.ρ (fun γ => (hm.cV j).2.1 γ) D.what₂.embLL (A.MtCSD j t) (R.B.L j t).pres (A.heckeL j t)
      (R.B.L j t).hecke (hf.degL j t)
    exact ⟨⟨lifts_opMat_mem R hf j t, h.1⟩, h.2⟩

end GlobalTheory.SplitHeckeCore

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem hecke_operators_rational_adjoint_closed_of_weak_char : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH) ∧ ∀ j t, (A3.A.fam.L j t).OkH := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC
  have h := GlobalTheory.SplitHeckeCore.hecke_okH_comm R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models
  exact ⟨fun t => (h.1 t).1, fun j t => (h.2 j t).1⟩

end GlobalTheory.Hk3

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertOkH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem csum_zero_left {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (g : S.Cl → S.V) : S.csum 0 g = 0 := by
  simp [CSD.csum]

theorem csum_zero_right {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (f : S.Cl → S.V) : S.csum f 0 = 0 := by
  simp [CSD.csum]

set_option maxHeartbeats 4000000 in

theorem inertHeckeOperators_rows_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (t : T) :
    (A3.rowI t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hR t
  have hrk : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := R.toRealDat.B.rankR
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents D.sp.X'.rank (Formalism.IndefR.Links.labIn D.sp.X'.rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeRI t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk D.sp.X'.rank s' ∧ A3.heckeRI t k = A3.heckeRI t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.R t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtildeCSD t).basis (A3.A.MtildeCSD t).basis (A3.heckeRI t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.rowI t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.rowI t).opI k = A3.heckeRI t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g

set_option maxHeartbeats 4000000 in

theorem inertHeckeOperators_lifts_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (j : Fin D.R.m) (t : T) :
    (A3.liftI j t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hL j t
  have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.toRealDat.B.rankL j
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models j t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn (Vc D j).rank i.2) (A3.heckeLI j t)
    (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (Formalism.IndefR.Links.labIn (Vc D j).rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeLI j t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk (Vc D j).rank s' ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.L j t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtCSD j t).basis (A3.A.MtCSD j t).basis (A3.heckeLI j t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.liftI j t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.liftI j t).opI k = A3.heckeLI j t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g

theorem heckeOperators_rows_lifts_rational_adjointClosed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hJ
  have h2 := hecke_operators_rational_adjoint_closed_of_weak_char R F hW
  exact ⟨fun t => ⟨h2.1 t, inertHeckeOperators_rows_rational_adjointClosed R F hW hJ t⟩, fun j t => ⟨h2.2 j t, inertHeckeOperators_lifts_rational_adjointClosed R F hW hJ j t⟩⟩

end GlobalTheory.InertOkH

end
end
