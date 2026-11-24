module

public import Formalism.PeriodIntegrals.SSAscent
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

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent

def TrNondeg {k : Type} [Field k] {a : ℕ} (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) : Prop :=
  ∀ x ∈ A, (∀ y ∈ A, Matrix.trace (x * y) = 0) → x = 0

def imAlg {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    Subalgebra k (Matrix (Fin a) (Fin a) k) :=
  Algebra.adjoin k (Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) k))

def TraceNilStep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (a : ℕ) (M : Matrix (Fin a) (Fin a) K),
    (∀ m : ℕ, 0 < m → Matrix.trace (M ^ m) = 0) → IsNilpotent M

def AscendStep : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (a : ℕ) (S : Set (Matrix (Fin a) (Fin a) K)),
    TrNondeg (Algebra.adjoin K S) →
      TrNondeg (Algebra.adjoin L ((algebraMap K L).mapMatrix '' S))

def DownStep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    IsSSRep ρ → TrNondeg (imAlg ρ)

def UpStep : Prop :=
  ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) k),
    TrNondeg (imAlg ρ) → IsSSRep ρ

end PI.SSAscent.UnitaryGroupMassFormula
