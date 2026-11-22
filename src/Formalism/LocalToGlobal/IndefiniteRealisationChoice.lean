module

public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.KernelLattices.KerChTie
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.KerMemPin
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.GroupLattices.JointServices.Cut
public import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
public import Formalism.SharpRestriction.Divisibility.HookProducts.Compl3Record

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top4

open Formalism.L2.Top3

section SelTieS

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

end SelTieS

structure KsChoice (D : D7) where
  Ks : Type
  [f : Field Ks]
  [n : NumberField Ks]
  [a : Algebra Ks D.what₂.LL]

attribute [instance] KsChoice.f KsChoice.n KsChoice.a

section At

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end At

open Formalism.L2.DIV in
structure RemainingDivisionBounds {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) : Prop where

  hh : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

theorem cut_of_stable {eps : ℝ} {Fm : FamP eps}
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i μ _ => Formalism.L2.G.ServJoint.cutUp_of_stable _ μ fun a y hy => h x hx i μ a y hy⟩

end Formalism.L2.Top4

end
