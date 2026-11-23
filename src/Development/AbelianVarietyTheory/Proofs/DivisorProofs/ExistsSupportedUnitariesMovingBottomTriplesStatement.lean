module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriples
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ t : T,
    ∃ (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
      (Formalism.L2.Theta.SuppAt (Y.e t) A g ∧ Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A g x) ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) A' g' ∧ Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x') ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) WW h ∧ Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) WW h y) ∧
      (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) ∧
      ∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
        frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u := by
  first | exact @GlobalTheory.BotUnitMove.move_elts | exact GlobalTheory.BotUnitMove.move_elts | (intros; apply GlobalTheory.BotUnitMove.move_elts <;> assumption)
