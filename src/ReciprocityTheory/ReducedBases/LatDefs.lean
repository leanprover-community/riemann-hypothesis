module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ReducedBases

open Matrix

def toReal {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => (x i : ℝ)

def polar {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℤ) : ℝ :=
  toReal x ⬝ᵥ (A *ᵥ toReal y)

def Q {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : ℝ := polar A x x / 2

def SameClass {d : ℕ} (N : ℤ) (a b : Fin d → ℤ) : Prop := ∃ w : Fin d → ℤ, a = b + N • w

def IsMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, F a ≤ F (a + N • w)

def IsUniqueMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, w ≠ 0 → F a < F (a + N • w)

end ReciprocityTheory.ReducedBases

end
