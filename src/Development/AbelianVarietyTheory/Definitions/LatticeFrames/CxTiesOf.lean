module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
public import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}

def DcPtG {ex : Extra D L hT Gi Gl Kc Yd cX} (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

attribute [instance] RealPack.fKs RealPack.nKs RealPack.aKs

variable {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiS

end
