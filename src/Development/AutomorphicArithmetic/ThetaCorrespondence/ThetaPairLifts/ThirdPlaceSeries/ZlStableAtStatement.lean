import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegralStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMemberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMemberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralCharacterIntegral

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenRatAt
section Main
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Main
theorem cenRat_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r
end GlobalTheory.CenRatAt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenRat_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  atlas_forward_decl _root_.GlobalTheory.CenRatAt.cenRat_at_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenLocAt
section Gen
open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
end Gen
theorem actRead_at_mem_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok
end GlobalTheory.CenLocAt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actRead_at_member_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y := by
  atlas_forward_decl _root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩
set_option maxHeartbeats 2000000 in
theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenLoc_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := by
  atlas_forward_decl _root_.GlobalTheory.CenLocAt.cenLoc_at_member
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenIntAtLoc
open Formalism.L2.DIV
end GlobalTheory.CenIntAtLoc
namespace GlobalTheory.CenIntAtLoc
theorem cenInt_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ w Z _ _ t _ _ _ _ _ hR _ => ?_
  obtain ⟨r⟩ := hR
  refine cenInt_of_allT r.all (InfinitePlace.mk (w.st Z).B.embLL) (GlobalTheory.Mem.R3.OkVals.isConjAt_embLL _) (fun k τ => ?_) (fun k τ => ?_)
  · exact (Formalism.L2.Col.mtK_rat _ _ _ τ.1 t.hX ((k : ℕ) + 1)).posH _ _
  · exact Formalism.L2.Col.unipotentActionClassSum_good _ _ _ τ.1 t.hX ((k : ℕ) + 1) _
end GlobalTheory.CenIntAtLoc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenInt_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  atlas_forward_decl _root_.GlobalTheory.CenIntAtLoc.cenInt_at_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenAtLoc
theorem zlStable_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.ZLStable (w.D Z) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR _ => hR.elim fun r => zlStable_of_allT r.all
theorem cen_loc_zl_stable_cen_int : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => CenLoc (w.D Z) c.a.all.gal.mt ∧ GlobalTheory.PendOf.ZLStable (w.D Z) ∧ GlobalTheory.PendOf.CenInt (w.D Z) := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenLoc_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.CenAtLoc.zlStable_at_alt hL) (_root_.GlobalTheory.T.cenInt_at_members hL))
end GlobalTheory.CenAtLoc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => CenLoc (w.D Z) c.a.all.gal.mt ∧ GlobalTheory.PendOf.ZLStable (w.D Z) ∧ GlobalTheory.PendOf.CenInt (w.D Z) := by
  atlas_forward_decl _root_.GlobalTheory.CenAtLoc.cen_loc_zl_stable_cen_int
end
end
