module

public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_conj {D : D7} (x : D.host.E) : star x = D.host.conj x := bridge_star_holds D.R D.host x

def GIwPos {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) (Kp.iw 0 v x)) =
      c.embW u w hg (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (if s.val % 2 = 1 then D.host.conj x else x))

end Formalism.L2.Herm

end
