module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def RowDivClosed {R : Type*} [CommRing R] {r n : ℕ} (M : Submodule R (MvPolynomial (Fin r × Fin n) R)) : Prop :=
  ∀ (a b : Fin r) (k : ℕ), ∀ f ∈ M, rowDiv R a b k f ∈ M

def fockQ {σ : Type*} (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)

def HWLine : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ f ∈ dualWeyl K r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv K a b k f = 0) →
      ∃ c : K, f = c • hw K hn ν

def HWLineTall : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r n : ℕ) (ν : Fin n → ℕ),
    (∃ s : Fin n, r ≤ s.val ∧ 0 < ν s) →
    ∀ f ∈ dualWeyl K r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv K a b k f = 0) → f = 0

def FockQPos : Prop :=
  ∀ (σ : Type) (f g : MvPolynomial σ ℚ), fockQ f g = fockQ g f ∧ (f ≠ 0 → 0 < fockQ f f)

def FockQBilin : Prop :=
  ∀ (σ : Type) (f f' g : MvPolynomial σ ℚ) (c : ℚ),
    fockQ (f + f') g = fockQ f g + fockQ f' g ∧ fockQ (c • f) g = c * fockQ f g

def FockQRowDivAdj : Prop :=
  ∀ (r n : ℕ) (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) ℚ),
    fockQ (rowDiv ℚ a b k f) g = fockQ f (rowDiv ℚ b a k g)

def RowDivClosedGraded : Prop :=
  ∀ (r n : ℕ) (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)), RowDivClosed M →
    ∀ f ∈ M, ∀ μ : Fin r → ℕ, weightedHomogeneousComponent (rowW r n) μ f ∈ M

def HWInClosed : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ), M ≤ dualWeyl ℚ r n ν → RowDivClosed M → M ≠ ⊥ →
      hw ℚ hn ν ∈ M

def ClosedEqNabla : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ), M ≤ dualWeyl ℚ r n ν → RowDivClosed M →
      hw ℚ hn ν ∈ M → M = dualWeyl ℚ r n ν

def WeylEqNablaQ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → weyl ℚ r n hn ν = dualWeyl ℚ r n ν

def WeylRationalOf : Prop := WeylEqNablaQ → WeylRational

end Formalism.GradedWeylDivisibility
