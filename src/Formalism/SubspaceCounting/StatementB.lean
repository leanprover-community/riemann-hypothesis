module

public import Mathlib.LinearAlgebra.Dimension.Finrank
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

noncomputable section

open scoped BigOperators

namespace Formalism.G0

def window (n i L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j => (i + j) % n

def CondA (n : ℕ) (T : Finset ℕ) (L₂ K : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i L₂).card ≤ K

def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)

def countAbove {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // A ≤ U ∧ Module.finrank F U = j}

def countBelow {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // U ≤ A ∧ Module.finrank F U = j}

def SubspaceCount : Prop :=
  ∀ {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W] (k : ℕ),
    countBelow (⊤ : Submodule F W) k = gaussBinom (Fintype.card F) (Module.finrank F W) k

def TypeIIUp : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (countAbove (LinearMap.range f) j : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ (l * (N + l - j)) * gaussBinom (Fintype.card F) g l *
          Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧
            Module.finrank F U + (j - l) = N}

def TypeIIDown : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (Nat.card {U : Submodule F Q // LinearMap.range f ≤ U ∧ Module.finrank F U + j = N + g} : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ ((j - l) * (g - l)) * gaussBinom (Fintype.card F) g l *
          countBelow (LinearMap.ker f) (j - l)

end Formalism.G0
