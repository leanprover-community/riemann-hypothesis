module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPow
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


theorem _root_.GlobalTheory.T.cauchy_product_partial_sums_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  first | exact @GlobalTheory.cauchy_product_dvd_pow | exact GlobalTheory.cauchy_product_dvd_pow | (intros; apply GlobalTheory.cauchy_product_dvd_pow <;> assumption)
