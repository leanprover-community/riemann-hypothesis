module

public import Formalism.CMTypeGalois.StatementField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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

open NumberField Ideal Filter Topology Finset Formalism.Q3

noncomputable section

namespace Formalism.HF

def LogDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n))
    (𝓝[>] 1) (𝓝 δ)

def QuadDiscr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K),
    x ^ 2 = (a : K) → IntermediateField.adjoin ℚ {x} = ⊤ → Squarefree a → a % 4 = 1 →
    discr K = a

def MQDiscr : Prop :=
  ∀ (k : ℕ) (q : Fin k → ℕ), 1 ≤ k → (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
  ∀ (E : Type) [Field E] [NumberField E] (α : Fin k → E), IsMQ (fun i => -(q i : ℤ)) α →
    discr E = (-1) ^ (2 ^ (k - 1)) * ∏ i, (q i : ℤ) ^ (2 ^ (k - 1))

def APLogDensity : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
    LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ))

end Formalism.HF
