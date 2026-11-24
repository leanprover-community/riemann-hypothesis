module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteHomogeneousGeneratorsGradedSubgroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  first | exact @GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | exact GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | (intros; apply GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators <;> assumption)
