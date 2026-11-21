import Mathlib
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas
import Formalism.SharpRestriction.Divisibility.HookProducts.NormAtEqSqrtMajAt
import Formalism.SharpRestriction.Divisibility.HookProducts.LambdaZeroLeFourB

open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.MainNotions

def FunSharpRec : Prop :=
  ∀ (D : D7) (X0 : BaseLevelRowSide D) (Y : DivX D) {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
    {Sp : SPer Dc} {N : IndefNum Bs} (P : IndefCoreR Df0 Df1 Dc Sp N)
    (eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V),
    HLatTie X0.s.RR P.base.RR P.base.XE eRR0 →
    (∀ e : D.what₂.LL →+* ℂ, Y.kapR e = P.cols.κ (InfinitePlace.mk e)) →
    ∀ C : ℝ, C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 →
    LemmaT D X0 C →
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤ N.hh + 14 * lam0 D


structure FunDat (D : D7) (X0 : BaseLevelRowSide D) where
  Bs : DefBase D.what₂.LL
  Df0 : DefSide Bs
  Df1 : DefSide Bs
  Dc : DefCols Df1
  Sp : SPer Dc
  Z : IndefScale Bs
  Cp : ℝ
  CHp : ℝ
  P : IndefCoreR Df0 Df1 Dc Sp (Z.num Cp CHp)
  eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V

def FunTies {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (T : FunDat (Fm.D x i) (Fm.ex x hx i).p0) : Prop :=
  T.Z.x = (Fm.L x i).sc.x ∧ T.Z.b = (Fm.L x i).sc.b ∧ T.CHp ≤ CHf Fm.cOut ∧
    HLatTie (Fm.ex x hx i).p0.s.RR T.P.base.RR T.P.base.XE T.eRR0 ∧
    ∀ e : (Fm.D x i).what₂.LL →+* ℂ, (Fm.X x i).kapR e = T.P.cols.κ (InfinitePlace.mk e)

def sharpFunctionalExponent (CHf : List ℝ → ℝ) : List ℝ → ℝ := fun l => max (CHf l) 1 + 1

def FunSharpFam : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ)
    (Pt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FunDat (Fm.D x i) (Fm.ex x hx i).p0),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Pt.1 ≤ x) (i : Fm.Ix x), FunTies Fm CHf x hx i (Pt.2 x hx h i)) →
    Formalism.MainNotions.PrimeDegreeVariant.SlopeLossFamily Fm →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ sharpFunctionalExponent CHf Fm.cOut * (Fm.L x i).sc.b



end Formalism.MainNotions.DIV.HookProducts
