module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero
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

abbrev IM (X : Loc) := (Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕
  ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j) × Fin X.m) ⊕ ((Σ j : Fin (numSeg X.TT), Fin (segS X.TT j)) ⊕ Fin X.m))

def multMk (X : Loc) (β : GlobalTheory X) : IM X → ℕ
  | Sum.inl x => (β x.1).sg x.2
  | Sum.inr (Sum.inl x) => (β x.1).rz x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => (β x.1).ry x.2 0
  | Sum.inr (Sum.inr (Sum.inr _)) => X.c

def fMk (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → RHH O X
  | Sum.inl x => kSkey O X x.1 x.2 ^ (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl x) => kWkey O X x.1 x.2.1 x.2.2.succ
  | Sum.inr (Sum.inr (Sum.inl x)) => kSkey O X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr c)) => locC O X c.succ

def aMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → MonH X
  | Sum.inl x => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ segG X.TT x.1) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) ((X.seg C0 CE1 CE2 x.1).P X.p x.2)
  | Sum.inr (Sum.inl x) => Finsupp.single ((topOdd X x.1 x.2.1, true), x.2.2.succ) 1 +
      Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2.1)
  | Sum.inr (Sum.inr (Sum.inl x)) => Finsupp.single ((topStart X x.1, true), 0) (X.p ^ (segDists X.TT x.1).get x.2) +
      Finsupp.single ((topOdd X x.1 x.2, false), 0) 1
  | Sum.inr (Sum.inr (Sum.inr _)) => ∑ j : Fin (numSeg X.TT), Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j - 1)

def oMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → ℕ
  | Sum.inl x => (X.seg C0 CE1 CE2 x.1).P X.p x.2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

def dgMk (C0 CE1 CE2 : ℝ) (X : Loc) : IM X → X.TT × Bool → ℕ
  | Sum.inl x => fun l => (X.seg C0 CE1 CE2 x.1).P X.p x.2 * dgKS X x.1 x.2 l
  | Sum.inr (Sum.inl x) => dgKW X x.1 x.2.1
  | Sum.inr (Sum.inr (Sum.inl x)) => dgKS X x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr _)) => dgLoc X

def bMk (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  Finsupp.single ((topStart X j, true), 0) (X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1))) +
    (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

end Formalism.MainNotions.ColumnSystems.Pf
