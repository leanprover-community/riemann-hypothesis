module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

def IsStageC (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ pp D j ∧ q ≤ qq D j ∧ A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * qq D j = rankV D i j + 2 * q ∧ NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (fun t => nuH G t i j) (locPl G)

theorem negIdx_of_isStd {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) : NegIdx V 0 := fun τ => by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]
  refine ⟨(Equiv.sumEmpty _ _).symm, 1, ?_⟩
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  all_goals first | exact a.elim0 | exact b.elim0

theorem IsBottomTri.isStageC {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) : IsStageC W i j 0 0 X := by
  have r := ranks_exact D i j
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, negIdx_of_isStd h.std, negIdx_of_isStd h.std',
    negIdx_of_isStd h.stdW, h.is⟩
  · rw [h.rank]; simpa [pp] using r.1
  · rw [h.rank']; simpa [qq] using r.2.1

end GlobalTheory.SqTower
