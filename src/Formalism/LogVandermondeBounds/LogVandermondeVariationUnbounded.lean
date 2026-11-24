module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def CardGeneralLinear : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * (n - 1) / 2) * (Fintype.card F : ℝ) ^ (n * (n + 1) / 2) *
        ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1))

def CardUnitriangular : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    Nat.card {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} =
      Fintype.card F ^ (n * (n - 1) / 2)

def EulerProductBounds : Prop :=
  ∀ (q : ℝ), 3 ≤ q → ∀ n : ℕ,
    1 / 2 ≤ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ∧ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ≤ 1

def CardStabilizerVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (v : Fin n → F), v ≠ 0 →
    Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} *
      (Fintype.card F ^ n - 1) = Fintype.card (GL (Fin n) F)

def PrimeOrderFinrank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (A : Matrix (Fin n) (Fin n) K),
    g.Prime → A ^ g = 1 → A ≠ 1 → g - 1 ≤ Module.finrank ℚ K * n

end Formalism.LogVandermondeBounds.StandardLattice
