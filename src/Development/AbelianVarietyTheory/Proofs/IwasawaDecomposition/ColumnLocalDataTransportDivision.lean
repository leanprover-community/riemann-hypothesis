module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open GlobalTheory.Mem.Db

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)



def nchTTr {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) :
    NchT w (setDivZ Z N h) Wt { nch with } :=
  { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }



def kerTr {Gt : GatTies (w.D Z)} {cmp : LatCmp (w.D Z)} {Gy : G.LatInst (w.D Z)} (k : KerFam (w.D Z) Gt cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) { Gt with } { cmp with } (w.tw (setDivZ Z N h)) { Gy with } :=
  fun u v g => { k u v g with }



def columnLocalDataTransportDivision (c : ColumnDataSplitPrimes K w Z)
    (hR : let t := DivTr.colTTr w Z N h c.toColT
          IsRecG K.s (w.D (setDivZ Z N h)) t.Gt t.cmp t.g.herm t.g.forms) :
    ColumnDataSplitPrimes K w (setDivZ Z N h) :=
  { DivTr.colTTr w Z N h c.toColT with isRec := hR, om := c.om }

end GlobalTheory.Mem.Top.Bl.WitTr

end
