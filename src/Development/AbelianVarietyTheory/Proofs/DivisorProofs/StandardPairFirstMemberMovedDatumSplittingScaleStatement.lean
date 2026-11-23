module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScale
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

theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  first | exact @GlobalTheory.BotFrames.move_fst | exact GlobalTheory.BotFrames.move_fst | (intros; apply GlobalTheory.BotFrames.move_fst <;> assumption)
