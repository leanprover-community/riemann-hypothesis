module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTuple
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove


theorem _root_.GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  first | exact @GlobalTheory.BotScal.moved_vacua_scal | exact GlobalTheory.BotScal.moved_vacua_scal | (intros; apply GlobalTheory.BotScal.moved_vacua_scal <;> assumption)
