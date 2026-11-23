module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRangeOfPowG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermEqExtraTied
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {B : Base} {C : Cols B} {Z : Later B C} (Z' : Later B C)



def forms0Re {u : B.Word} (T : Forms0 (recOf Z) u) : Forms0 (recOf Z') u :=
  { T with
    atT := atTTRe Z' T.atT
    cls0 := clsRe Z' T.cls0
    val0 := valRe Z' T.val0
    lv0 := lvRe Z' T.lv0 }


theorem columnFormsAlongLaterStages_stageZero_eq (T : ColsTiedSym (recOf Z)) (u : B.Word) :
    ((colsRe Z' T).forms u).to0 = forms0Re Z' (T.forms u).to0 := rfl


open Formalism.MainNotions.G in

theorem forms0Re_setGat (g : ∀ u (w : (recOf Z).what₂.places.Pl),
      GIdx (recOf Z).host ((recOf Z).mem u).A.T ((recOf Z).what₂.places.resChar w) → GAtP ((recOf Z).what₂.places.resChar w))
    (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ ((recOf Z).mem u).A.Mu0) {u : B.Word} (T : Forms0 (recOf Z) u) :
    forms0Re { Z with G := { Z.G with gat := g, gat_d := hd } } T = Formalism.L2.G.forms0Set (recOf Z) g hd T := rfl

end Re

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section Std

variable (l : I.Laws) {Z : Later B (I.cols l)} (Z' : Later B (I.cols l))



theorem stdC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (h : I.StdC l Z T) : I.StdC l Z' (colsRe Z' T) := fun u =>
  { h u with gl := { (h u).gl with } }



theorem stdLvC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (u : B.Word) (h : I.StdLvC l Z u (T.forms u)) :
    I.StdLvC l Z' u ((colsRe Z' T).forms u) := h

end Std

variable (h : I.Ok) (p : TC.Pins B X) (l : I.Laws)

variable (Z : Later B (I.cols l))

theorem dGam_cols (u : B.Word) (a : I.ι) : ((I.cols l).chTw u a).DGam = DGam B.fields.E B.R := rfl

theorem colLay_of_tie (T : ColsTiedSym (I.rec7 l Z)) : ColLay (I.rec7 l Z) T.herm.base.lev0 (errOf T.herm) :=
  colLay_of_tied ⟨B, I.cols l, Z.W, Z.V, Z.S, Z.N, Z.G⟩ ⟨X⟩ (dGam_cols I l) T


open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in
theorem colLay_colT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z),
    ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  intro B f T w Z t
  have e : errOf t.C.herm = Formalism.L2.Herm.toErrXS t.full.1 :=
    GlobalTheory.Mem.Col2.TC.ExtraTie.errX_eq t.full.1 t.C.herm t.full.2 (errOf t.C.herm) (errOf_piG _) (errOf_piT _) (errOf_vPl _)
  have hl : t.full.1.base.lev0 = t.C.herm.base.lev0 :=
    congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) t.full.2
  rw [hl, ← e]
  exact colLay_of_tie w.I w.l Z t.C

end GlobalTheory.Mem.Top.ColOwe

end
