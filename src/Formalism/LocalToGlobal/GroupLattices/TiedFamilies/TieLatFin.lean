import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieDim
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieWeak
import Formalism.LocalToGlobal.GroupLattices.FockModels.Sandwich
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount

section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}
  {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem card_eq_d (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fintype.card ((D.fm u).lat 0).ι = Module.finrank (D.gat u w hg).O (D.gat u w hg).M := by
  have h1 : Module.finrank ℂ ((D.fm u).Fi 0) = Fintype.card ((D.fm u).lat 0).ι := by
    rw [← ((D.fm u).emb_basis 0).2]
    exact finrank_span_eq_card ((D.fm u).emb_basis 0).1
  have h2 : Module.finrank ℂ ((D.fm u).Fi 0) = Module.finrank ℂ (D.mem u).A.Mu0 :=
    congrArg (fun S : Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) => Module.finrank ℂ S) (D.fm u).Fi_zero
  exact h1.symm.trans (h2.trans (D.gat_d u w hg).symm)

def cmpLin (H : CmpCore T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V →ₛₗ[I.embW u w hg] (D.gat u w hg).Fn :=
  cmpL (e := I.embW u w hg) (H.ex u w hg) (valUniq_of (embT_conj D) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B))

theorem cmpLin_mem_span (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V) :
    cmpLin H u w hg x ∈ Submodule.span (D.gat u w hg).Kf ((D.gat u w hg).M : Set (D.gat u w hg).Fn) := by
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    exact (cmpRec_lat_pf H hloc u w hg y).2 (Submodule.subset_span hy)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ h1

set_option maxHeartbeats 1000000 in

theorem surjRat_pf (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I)
    (hfrac : ∀ u w hg, IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hfin : ∀ u w hg, Module.Finite (D.gat u w hg).O (D.gat u w hg).M) : SurjRat T Gt I := by
  intro u w hg F hF hrat
  have := hfrac u w hg
  have := hfin u w hg
  have hli : LinearIndependent (D.gat u w hg).Kf fun a => cmpLin H u w hg (((D.fm u).lat 0).b a) :=
    cmpC_li (e := I.embW u w hg) (embT_conj D) (H.ex u w hg)
      (valUniq_of (embT_conj D) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B)) (ptAll_rec X T u (H.same u) w hg I.B)
      (embFr_inj T u) ((D.fm u).lat 0).b ((D.fm u).lat 0).b.linearIndependent
  have h1 : F ∈ Submodule.span (D.gat u w hg).Kf (Set.range fun a => cmpLin H u w hg (((D.fm u).lat 0).b a)) :=
    mem_span_of_card (D.gat u w hg).M _ hli (fun a => cmpLin_mem_span H hloc u w hg _) (card_eq_d D u w hg) F hF
  have h2 : F ∈ Submodule.span (D.gat u w hg).Kf (Set.range (cmpLin H u w hg).toAddMonoidHom) := by
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  exact rat_mem (I.embW u w hg) (evG (D.gat u w hg)) (cmpLin H u w hg).toAddMonoidHom (evG_sep _)
    (fun a x => (cmpLin H u w hg).map_smulₛₗ a x) (fun x => (ratFn_iff _ _ _).1 (cmpC_rat x)) h2
    ((ratFn_iff _ _ _).1 hrat)

end Formalism.L2.G
end
end

section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem htupW_le_htup (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : (D.gat u w hg).P.Tup) :
    (D.gat u w hg).P.HtupW L ≤ (D.gat u w hg).P.Htup L := by
  have hW := Formalism.MainNotions.G.Joints.weylSandwich_of_model D (Formalism.L2.G.Model.modelSandwichG_of_ties D Gt)
  refine Submodule.span_mono ?_
  rintro Z ⟨F, hF, rfl⟩
  refine ⟨F, fun v => ?_, rfl⟩
  refine (Submodule.span_mono ?_ : HtenW (D.gat u w hg).O _ _ ≤ Hten (D.gat u w hg).O _ _) (hF v)
  rintro Y ⟨F', hF', rfl⟩
  exact ⟨F', fun s => (hW u w hg _ _ _).2 (hF' s), rfl⟩

theorem m_le_mna (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (D.gat u w hg).M ≤ (D.gat u w hg).Mna := by
  intro F hF
  have h1 := (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.HtupW F).1 hF
  refine (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.Htup F).2 fun i => ?_
  exact ⟨fun L hL => htupW_le_htup Gt u w hg L ((h1 i).1 L hL), (h1 i).2⟩

theorem m_finite_rec (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (h : (D.gat u w hg).FinClasses) :
    Module.Finite (D.gat u w hg).O (D.gat u w hg).M :=
  Formalism.MainNotions.FormalGroupSystem.Pf.m_finite (D.gat u w hg) h (m_le_mna Gt u w hg)

variable {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem surjRat_rec (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    SurjRat T Gt I :=
  surjRat_pf H hloc (fun u w hg => frac_of_gatIs X.lev0 u w hg (hG u w hg))
    (fun u w hg => m_finite_rec Gt u w hg (finClasses_of_gatIs X.lev0 u w hg (hG u w hg)))

theorem comparison_lattice_span_eq (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_rec' H hG hloc (surjRat_rec H hG hloc) u w hg

theorem cmpHyp0P_of_cmpCore (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    CmpHyp0P T Gt I where
  ex := H.ex
  evInj := fun u w hg => evInj_rec Gt I u w hg
  ptEx := fun u w hg => ptEx_rec X T u w hg I.B
  ptAll := fun u w hg => ptAll_rec X T u (H.same u) w hg I.B
  chi := H.chi
  latM := comparison_lattice_span_eq H hG hloc

end Formalism.L2.G
end
end
