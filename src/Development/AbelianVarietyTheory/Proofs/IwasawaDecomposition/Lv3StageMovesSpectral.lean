import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLatticeStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Mv

section
variable {B : Base} {C : Cols B} {a : Late B C} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}
  {R : RealDat3 a.D A Ks} {F : Face3 a.D A} {X0 : BaseLevelRowSide a.D} {Y : Read (A3 := A) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)
  (u : Parts R)

theorem jWu_heq : HEq (jWu Z u) Z.jW := (by with_unfolding_all exact ((HEq.refl Z.jW) :))

theorem eRRu_heq : HEq (eRRu Z u) Z.eRR := (by with_unfolding_all exact ((HEq.refl Z.eRR) :))

theorem eRR0u_heq : HEq (riemannRochSpaceCoordinateEquiv Z u) Z.eRR0 := (by with_unfolding_all exact ((HEq.refl Z.eRR0) :))

variable (c : Refill a)

theorem readL_jW : HEq (letI := alg c.to iK; (readL c Z).jW) Z.jW := (by with_unfolding_all exact ((jWu_heq Z (partsB c R)) :))

theorem readL_eRR : HEq (letI := alg c.to iK; (readL c Z).eRR) Z.eRR := (by with_unfolding_all exact ((eRRu_heq Z (partsB c R)) :))

theorem transportedReading_baseRowLatticeCoordinates : HEq (letI := alg c.to iK; (readL c Z).eRR0) Z.eRR0 := (by with_unfolding_all exact ((eRR0u_heq Z (partsB c R)) :))

end

set_option maxHeartbeats 4000000 in

theorem rowsAre_refill : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  intro B C a c px I hX T Wt ix p0 r
  letI := r.z.alg
  refine ⟨⟨Mv.cpDat c.to c.same r.z, (by with_unfolding_all exact ((holds_tr c.to r.intersectionNumber_baseChange) :)), (by with_unfolding_all exact ((read c r.Y) :)), (by with_unfolding_all exact ((readL c r.Z) :)),
    (by with_unfolding_all exact (r.tup_ix :))⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB (HEq.refl r.Y.tup)
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.tupT) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.PY.ψ) :))
  · exact (by with_unfolding_all exact ((HEq.refl (fun i => (r.Y.PW i).ψ)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (funext fun π => (rep_eq c r.Y π).symm)) :))
  · kexactB (HEq.refl (fun x => (r.Y.Ish.jE x).1))
  · kexactB (HEq.refl (fun x => (r.Y.Iz.jE x).1))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.eE) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.jA) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.jA0) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.eMt) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.mj.eW) :))
  · exact (by with_unfolding_all exact ((readL_jW r.Z c) :))
  · exact (by with_unfolding_all exact ((readL_eRR r.Z c) :))
  · exact (by with_unfolding_all exact ((transportedReading_baseRowLatticeCoordinates r.Z c) :))

end GlobalTheory.Mem.R3.Rw.Mv

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.Mv.rowsAre_refill
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Up

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T₀ D.R.m}

theorem exists_mjHTie_of_eq (F : Face3 D A3) (Xd : DivX D) {X X' : Cx.CxData A3.fam3.amb3} (e : X' = X)
    (jW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (jW0 : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (hj : HEq jW jW0)
    (eW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (h1 : ∀ (i : Fin D.R.m) x, Xd.jM ((i : ℕ) + 1) (eW i x) = jW i x)
    (h2 : ∀ i : Fin D.R.m, HLatTie (Xd.MjH ((i : ℕ) + 1)) ((A3.indefDown (X'.data F.cr false)).M i)
      ((A3.indefDown (X'.data F.cr false)).XW i) (eW i)) :
    ∃ J, MjHTie D A3.A Xd (A3.indefDown (X.data F.cr false)) jW0 J := by
  subst e
  cases hj
  exact ⟨⟨eW⟩, ⟨h1, h2⟩⟩

end GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.Up.mjAre_back : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  intro K B f T w Z hX Wt p0 r S' N h r' hz hj Y hY
  obtain ⟨z', hold', Y', Z', tix⟩ := r'
  dsimp only at hz hj
  subst hz
  obtain ⟨J', t'⟩ := hY
  letI : Algebra (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).core.Q.c.F (w.st (SRe.upL Z S' N h)).toD7.what₂.LL :=
    (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).alg
  have e := toCx3_eq (Up.refUp Z S' N h).to (iK := r.z.alg) r.z.R r.z.F
  exact (by with_unfolding_all exact ((exists_mjHTie_of_eq r.z.F (divBack Y) e.symm ((Z'.jW)) ((r.Z.jW)) ((hj)) ((J'.eW)) ((t'.j_eq)) ((t'.hlat))) : _))

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHermitianLattices_replacedStages_eq : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.Up.mjAre_back
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem rxs_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  intro K B f T w Z Wt p0 t S' N h t' hs ⟨x⟩
  have hstd : t'.r.z.Std := (GlobalTheory.T.standardReading_transport_and_extension_trans).1 B f T w Z (SRe.upL Z S' N h) t.hX Wt t.r.z t'.r.z hs.Xg hs.tr hs.R hs.core x.std
  obtain ⟨hX', r', exAt', inGeo', grpAt', grp', mu'', exact', untw', emt0', emt', etaF', rowInt', idx'⟩ := t'
  obtain ⟨z', holds', Y', Z'', tup_ix'⟩ := r'
  obtain @⟨Xg', tr', core', alg', alg_eq', R', cG', geo', pins', lev', idG', good', mu', le', Ks'⟩ := z'
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hcG := hs.cG
  have htup := hs.tup
  have hjA := hs.jA
  have hjA0 := hs.jA0
  have heMt := hs.eMt
  clear hs
  dsimp only at hXg htr hcore hR hcG htup hjA hjA0 heMt hstd
  subst hXg htr
  have hc := eq_of_heq hcore
  subst hc
  have ha : @Eq _ alg' t.r.z.alg :=
    Algebra.algebra_ext _ _ fun r => B.embLL.injective ((alg_eq' r).trans (t.r.z.alg_eq r).symm)
  subst ha
  have hr := eq_of_heq hR
  cases hr
  have hg := eq_of_heq hcG
  cases hg
  cases Y' with
  | mk tup' tupT' tupT_tup' tupTie' tup0' muAt' hm' hTop' hinj' Ish' Iz' IL' Kc' PY' PW' eFT' ιW' tied' prtE' prtE0' prtWE' xi'
      isomFin' frameMatch' hF' stdPsi' jA' jA0' eMt' => ?_
  dsimp only at htup hjA hjA0 heMt
  have e1 := eq_of_heq htup
  cases e1
  have e2 := eq_of_heq hjA
  cases e2
  have e3 := eq_of_heq hjA0
  cases e3
  have e4 := eq_of_heq heMt
  cases e4
  exact ⟨{
    all := {
      jA := (by with_unfolding_all exact (x.all.jA :))
      jA0 := (by with_unfolding_all exact (x.all.jA0 :))
      eMt := (by with_unfolding_all exact (x.all.eMt :))
      formsA := (by with_unfolding_all exact (x.all.formsA :))
      latA := (by with_unfolding_all exact (x.all.latA :))
      formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
      latA0 := (by with_unfolding_all exact (x.all.latA0 :))
      formsL := (by with_unfolding_all exact (x.all.formsL :))
      latL := (by with_unfolding_all exact (x.all.latL :))
      cen := (by with_unfolding_all exact (x.all.cen :)) }
    jA_use := (by with_unfolding_all exact (x.jA_use :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact (x.movedReadingSameMaps_baseReading_agrees :))
    eMt_use := (by with_unfolding_all exact (x.eMt_use :))
    e := (by with_unfolding_all exact (x.e :))
    eMt0 := (by with_unfolding_all exact (x.eMt0 :))
    eMtTw := (by with_unfolding_all exact (x.eMtTw :))
    crd := (by with_unfolding_all exact (x.crd :))
    io := (by with_unfolding_all exact (x.io :))
    sha := (by with_unfolding_all exact (x.sha :))
    laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(SRe.upL Z S' N h).W, (SRe.upL Z S' N h).V, (SRe.upL Z S' N h).S, (SRe.upL Z S' N h).N, (SRe.upL Z S' N h).G⟩ (K := t.r.z.core.toCore) x.laws) :))
    canon := (by with_unfolding_all exact (x.canon :))
    rank := (by with_unfolding_all exact (x.rank :))
    pb := (by with_unfolding_all exact (x.pb :))
    std := (by with_unfolding_all exact (hstd :)) }⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCompatibilities_transport_replacedStages : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.Up.rxs_up
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem rows_up_at : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  obtain ⟨⟨z', hold', Y', Z'', tup'⟩, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages B w.C Z (refUp Z S' N h) _ w.I t.hX T Wt (Equiv.refl _) p0 t.r
  subst hz
  let r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I t.hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    ⟨_, hold', Y', Z'', tup'⟩
  have eW1 := Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (refUp Z S' N h).to (refUp Z S' N h).same t.r.z (F0K K.s (w.D (SRe.upL Z S' N h)))
  let t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    { hX := t.hX
      r := r'
      exAt := Mv.cp_exAt _ _ _ t.exAt
      inGeo := Mv.cp_inGeo _ _ _ t.inGeo
      grpAt := grpAt_up S' N h t.grpAt
      grp := t.grp
      mu := muIsW_up S' N h t.mu
      exact := (@Eq.trans (Set (@Rows.Places.Pl B.LL B.instLL B.places)) Wt (@Dat.W1 (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w Z))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@RowsT.exact B f T K w Z Wt p0 t) (@Eq.symm (Set (@Rows.Places.Pl (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.LL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.instLL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.places)) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) eW1))
      untw := (t.untw)
      emt0 := (t.emt0)
      emt := (t.emt)
      etaF := t.etaF
      rowInt := rowInt_up S' N h t.rowInt
      idx := fun Y hY => idxDefs_up (Z := Z) (S' := S') (N := N) (h := h) Y
        (t.idx (divBack Y) (GlobalTheory.T.liftHermitianLattices_replacedStages_eq K B f T w Z t.hX Wt p0 t.r S' N h r' rfl h13 Y hY)) }
  have hs : RowsSame t t' :=
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, (HEq.refl t.r.z.cG), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  refine ⟨t', hs, (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo)) :)), ?_, GlobalTheory.T.rowCompatibilities_transport_replacedStages K B f T w Z Wt p0 t S' N h t' hs⟩
  exact (by with_unfolding_all exact ((congrArg (fun e => ({ (SRe.pkOf t).up Z S' N h with eE := e } : SRe.RowPk (SRe.upL Z S' N h).D)) (eq_of_heq h8)) :))

theorem rows_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := fun K B f T w Z Wt p0 t S' N h =>
  let ⟨t', h1, h2, h3, h4⟩ := rows_up_at K B f T w Z Wt p0 t S' N h
  ⟨_, t', h1, h2, h3, h4⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.Up.rows_up
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

theorem kept_trans_layer {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''} (h : Kept c c') (h' : Kept c' c'') :
    Kept c c'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.forms.Fm.trans h'.forms.Fm, h.forms.acgFm.trans h'.forms.acgFm, h.forms.modFmK.trans h'.forms.modFmK, h.forms.modFmO.trans h'.forms.modFmO, h.forms.actG.trans h'.forms.actG, h.forms.U.trans h'.forms.U, h.forms.psiU.trans h'.forms.psiU, h.forms.eAlg.trans h'.forms.eAlg, h.forms.Dat.trans h'.forms.Dat, h.forms.th.trans h'.forms.th, h.forms.lev.trans h'.forms.lev, h.forms.thPsi.trans h'.forms.thPsi, h.forms.MtV.trans h'.forms.MtV, h.forms.acgMt.trans h'.forms.acgMt, h.forms.modMtK.trans h'.forms.modMtK, h.forms.modMtO.trans h'.forms.modMtO, h.forms.MtLat.trans h'.forms.MtLat, h.forms.thP.trans h'.forms.thP, h.forms.hkF.trans h'.forms.hkF⟩,
    h.br.trans h'.br, h.twI.trans h'.twI, h.sd.trans h'.sd, h.Q.trans h'.Q, h.k.trans h'.k, h.psi.trans h'.psi⟩

theorem org_of_kept {hL : GlobalTheory.Published.LocalLanglandsGL} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : Org hL cDep K w Wt nch) (hk : Kept nch nch') : Org hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩

set_option maxHeartbeats 4000000 in

theorem lv3Mv_true : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (prmR (NEo hL cDep) S Γ).s ∧ LevelThreeCondition (prmR (NEog hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨org_of_kept org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨org_of_kept org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩

end GlobalTheory.HeightCounting.Up
end
