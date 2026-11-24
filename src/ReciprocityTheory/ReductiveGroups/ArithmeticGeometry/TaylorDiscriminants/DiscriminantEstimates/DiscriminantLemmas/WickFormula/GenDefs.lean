module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

open MvPolynomial

namespace PI.WickFormula.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

noncomputable def gdelta (κ : I → J → K) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

noncomputable def dL (κ : I → J → K) (i : I) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ j, κ i j • (pderiv (Sum.inr j)).toLinearMap

end

def PowXL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inl i) * R) =
      X (Sum.inl i) * (gdelta κ ^ (n + 1)) R + (n + 1) • dL κ i ((gdelta κ ^ n) R)

def CommL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dL κ i R) = dL κ i ((gdelta κ ^ n) R)

def VanL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ i, m (Sum.inl i) < n) → (gdelta κ ^ n) R = 0

end PI.WickFormula.Gen
