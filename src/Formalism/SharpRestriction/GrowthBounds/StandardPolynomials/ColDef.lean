module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def lamS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → X.TT × Bool :=
  Fin.cons (topStart X j, true) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
    else (topEnd X j, true))

def posS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → ℤ :=
  Fin.cons ((segStart X.TT j).val : ℤ) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then ((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) : ℕ)
    else ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ))

def LLseg (X : Loc) (j : Fin (numSeg X.TT)) : LiftLetters (Fin (2 * segS X.TT j + 1 + 1)) where
  vec := fun i => (lamS X j i).2
  pos := posS X j

def zS (X : Loc) (j : Fin (numSeg X.TT)) : ℤ := ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ)

def phiS (X : Loc) (j : Fin (numSeg X.TT)) :
    Fin (2 * segS X.TT j + 1 + 1) × Fin (1 + X.m) → (X.TT × Bool) × Fin (X.m + 1) :=
  fun v => (lamS X j v.1, Fin.cast (Nat.add_comm 1 X.m) v.2)

end Formalism.MainNotions.ColumnSystems.Pf
