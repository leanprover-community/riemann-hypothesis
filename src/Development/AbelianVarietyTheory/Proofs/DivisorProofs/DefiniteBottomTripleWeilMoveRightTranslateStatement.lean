module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeilMoveRightTranslate
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (g : T → GA D A) (g' : T → GA D A') (h : T → GA D WW) (κ κ' : T → ℂ), (∀ t, κ t ≠ 0) → (∀ t, κ' t ≠ 0) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A (g t) ∧ Formalism.IndefR.Lev.finE A (g t) ∈ Formalism.L2.DIV.St Y.rA.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) A' (g' t) ∧ Formalism.IndefR.Lev.finE A' (g' t) ∈ Formalism.L2.DIV.St Y.rA'.β) →
    (∀ t, Formalism.L2.Theta.SuppAt (Y.e t) WW (h t) ∧ Formalism.IndefR.Lev.finE WW (h t) ∈ Formalism.L2.DIV.St Y.rW.β) →
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c →
      (GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW (fun t => κ t • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
        (fun t => κ' t • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t))).IsConst W.ψ W.θ fun t => κ t / κ' t * c t := by
  first | exact @GlobalTheory.BotTranslate.translate | exact GlobalTheory.BotTranslate.translate | (intros; apply GlobalTheory.BotTranslate.translate <;> assumption)
