module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
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

noncomputable section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

def ClassCountBoundAllPoints (𝒜 : FamClass) : Prop :=
  Closed (W1 𝒜) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def ClassCountBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ClassCountBoundAllPoints 𝒜

def H_jOn (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤

def JInvariantConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_jOn 𝒜

def H_la (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

def LambdaConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_la 𝒜

end GlobalTheory.Fc.R0

end
