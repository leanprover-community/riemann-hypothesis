module

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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.QD

open NumberField

def Arith : Prop :=
  ∀ (d : ℕ) (x y : ℚ), Squarefree d → d % 4 = 3 → (∃ u : ℤ, 2 * x = u) →
    (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N) → ∃ a v : ℤ, x = a + v / 2 ∧ y = v / 2

def IntCoeffs : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (x y : ℚ), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → IsIntegral ℤ ((x : K) + (y : K) * θ) →
    (∃ u : ℤ, 2 * x = u) ∧ (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N)

def Form : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K), θ ^ 2 = -(d : K) →
    Algebra.adjoin ℚ {θ} = ⊤ → ∀ z : K, ∃ x y : ℚ, z = x + y * θ

end PI.QD

end
