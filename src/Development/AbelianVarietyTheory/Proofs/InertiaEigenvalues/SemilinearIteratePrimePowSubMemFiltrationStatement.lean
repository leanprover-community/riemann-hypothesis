module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltration
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


theorem _root_.GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  first | exact @GlobalTheory.semilinear_iterate_prime_pow_sub_mem | exact GlobalTheory.semilinear_iterate_prime_pow_sub_mem | (intros; apply GlobalTheory.semilinear_iterate_prime_pow_sub_mem <;> assumption)
