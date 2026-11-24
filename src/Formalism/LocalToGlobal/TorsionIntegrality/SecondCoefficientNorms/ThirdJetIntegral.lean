module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.JetExpShape
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

namespace Formalism.L2.Th1.C

def LogDerivInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv : PowerSeries K),
    IsLogPair l linv → FGInt R l linv → IsOneUnit R (PowerSeries.derivative (R := K) l)

def ThirdJetIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph →
    IntPS R ((Dinv l)^[3] ph) ∧ ∀ i : ℕ, 3 ≤ i → jet l ph i ∈ R

def JetsUnramified : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    AdjAt R l linv ph a b → (a - b)⁻¹ ∈ R → a ≠ b →
    (∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R) ∧ ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R

def JetsShape : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    (∃ H : PowerSeries K, (∀ i : ℕ, jet l H i ∈ R) ∧
      (mvExp (-ph) : PowerSeries K) = mvExp (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) * H) ∧
    ∀ a b : K, AdjAt R l linv ph a b → (a - b) * jet l ph 2 ∈ R

end Formalism.L2.Th1.C
