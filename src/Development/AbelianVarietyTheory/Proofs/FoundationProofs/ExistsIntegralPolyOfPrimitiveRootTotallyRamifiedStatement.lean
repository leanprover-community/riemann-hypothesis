module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamified
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (K : Subfield Ω), (∀ x ∈ K, x ≠ 0 → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k) → ∀ (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) → ∀ u ∈ A, (∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, x ∈ K) ∧ Q.eval ζ = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ x ∈ K) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified | exact GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified | (intros; apply GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified <;> assumption)
