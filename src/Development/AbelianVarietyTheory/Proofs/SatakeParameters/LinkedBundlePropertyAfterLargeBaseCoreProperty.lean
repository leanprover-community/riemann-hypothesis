import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotLargeBaseConditionDisjoint
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnitaryRealisationReadingOfIdempotentActsViaLeve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsEOfHeq

noncomputable section

namespace GlobalTheory.NRows.AtPt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

def OverNE (N : NExt hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c)




def memberProperty (P : LayP hL) : V4.Slot := fun K X f T _ =>
  ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K X.B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
    P K X.B f T w Z Wt p0 t nch n c

abbrev AtWit (P : LayP hL) {p : Prm hL} {K : Ctx} (q : WPt p.s K) : Prop :=
  P K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n q.core

theorem largeBasePropertyG_memberProperty {P : LayP hL} (h : AtMem hL P) (Q : V4.Slot) : LargeBaseConditionG KPx Q (memberProperty P) :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ _ _ _ _ _ _ => H kp

section

variable {N : NExt hL} {S : SExt} {Γ : GeoP} {P : LayP hL}

theorem exists_wit_of_heq (hN : OverNE N) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit (prmR N S Γ).s K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt (prmR N S Γ).s K, q.Is D O ∧ EntC q.x.ker ∧ AtWit (p := prmR N S Γ) P q := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx, hP w Z _ _ _ _ _ _ x.nx.1 (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2) ⟨x.rx⟩ x.pin⟩

set_option maxHeartbeats 2000000 in

theorem exists_wit_pt (hN : OverNE N) (H : WitMv (prmR N S Γ).s) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (NE hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    {O : Obj2 (w.D Z)} (x : Wit (prmR N S Γ).s K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt (prmR N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ AtWit (p := prmR N S Γ) P q := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact exists_wit_of_heq hN hP (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy

set_option maxHeartbeats 2000000 in

theorem exists_wit (hN : OverNE N) (H : WitMv (prmR N S Γ).s) {K : Ctx} (β : BPt K)
    (hβ : β.Is (sAnd (IsGoodE (prmR N S Γ).s) (memberProperty P))) :
    ∃ q : WPt (prmR N S Γ).s K, q.Is β.D β.O ∧ EntC q.x.ker ∧ AtWit (p := prmR N S Γ) P q :=
  positionOf_ind (P := GoodE (prmR N S Γ).s) (R := fun K X f T c => memberProperty P K X f T c →
      ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt (prmR N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ AtWit (p := prmR N S Γ) P q)
    (fun _ _ _ _ _ _ _ g hP => g.1.elim fun b hb => exists_wit_pt hN H hP (b.wit g.2) hb)
    hβ.1 hβ.2 β.Y β.hY β.p

theorem of_is {𝒮 : Slots} {K : Ctx} {q : WPt 𝒮 K} {D : D7} {O : Obj D} (h : q.Is D O) {r : ∀ D : D7, Obj D → Prop}
    (hr : r (q.w.D q.Z) q.O) : r D O :=
  (congrArg (fun x : Σ D : D7, Obj D => r x.1 x.2) h).mpr hr

theorem rowE_memPosition (hN : OverNE N) (H : WitMv (prmR N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (prmR N S Γ).s K), EntC q.x.ker → AtWit (p := prmR N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    RowE (sAnd (IsGoodE (prmR N S Γ).s) (memberProperty P)) Lk fun _ D O _ _ => r D O :=
  RowE.of_all fun _ K β _ _ _ hβ _ => let ⟨q, a, b, c⟩ := exists_wit hN H β hβ; of_is a (hr K q b c)

end

theorem linkedBundleProperty_after_largeBaseCoreProperty {KP : BaseP} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd} {E : Par → BdP Bd} (h : LargeBaseConditionG KP Q R)
    (he : RowE (sAnd Q' R) Lk E) : Lg1 KP Q Q' fun U => RowE U Lk E :=
  ⟨_, GlobalTheory.Fc.LgModel.largeBaseProperty_conditional (R := R),
    ((EvP.of_evGd h).and he).mono fun _ _ _ t β q c b l => t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩




theorem lg1_entryPred_of_atMem_witMv {N : NExt hL} {S : SExt} {Γ : GeoP} {P : LayP hL} (h : AtMem hL P) (hN : OverNE N)
    (H : WitMv (prmR N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (prmR N S Γ).s K), EntC q.x.ker → AtWit (p := prmR N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    Lg1 KPx (IsBuiltE (prmR N S Γ).s) (IsGoodE (prmR N S Γ).s) fun U => RowE U Lk fun _ D O _ _ => r D O :=
  linkedBundleProperty_after_largeBaseCoreProperty (largeBasePropertyG_memberProperty h _) (rowE_memPosition hN H hr Lk)



end GlobalTheory.NRows.AtPt

end
