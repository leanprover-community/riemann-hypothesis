module

public import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
public import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
public import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in
def twPOf (P : RowSideFamily ex) (tupT : D.what₂.Tup → P.T) (tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ)
    (μ : D.what₂.Tup) (i : Fin D.R.m) (x : D.what₂.MtL μ ((i : ℕ) + 1)) :
    P.A3.A.fam.amb.FL i (tupT μ) :=
  if h : Formalism.IndefR.RecTie.Used0 D μ then
    (P.A3.A.fam.L i (tupT μ)).S.basis.equivFun.symm
      (((P.A3.A.fam.L i (tupT μ)).S.lvlE (P.A3.A.fam.L i (tupT μ)).r (P.A3.A.fam.lvlA P.P0 P.ψ0).P
          (P.A3.A.fam.lvlA P.P0 P.ψ0).ψ).mulVec
        ((P.I.eMt i (tupT μ)).symm ((tupTie μ h).symm ▸ x)))
  else 0

theorem dW_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.dW = S1.dW := by
  subst h
  cases hS
  rfl

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks} (Qr : RealRec Q)

end RealRec

namespace RealRec

variable {Q : RealT Rc P Dcf Spf Zscf S Ks}

end RealRec

end Formalism.IndefR
