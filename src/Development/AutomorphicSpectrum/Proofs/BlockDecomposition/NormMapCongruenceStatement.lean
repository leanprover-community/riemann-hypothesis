module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapCongruence
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.norm_map_congruence : ∀ (O S : Type) [CommRing O] [CommRing S] [Algebra O S] (I : Ideal O) [IsAdicComplete I S] (Q : ℕ → Ideal S) (N₀ : ℕ) (Nm : S → S) (t : S) (P₁ : Sˣ), (∀ m, Q (m + 1) ≤ Q m) → (∀ k, Q (N₀ * k + 1) ≤ Ideal.map (algebraMap O S) (I ^ k)) → Ideal.map (algebraMap O S) I ≤ Q 1 → (∀ x ∈ Q 1, IsUnit (1 + x)) → (∀ (k : ℕ) (x y : S), x - y ∈ Ideal.map (algebraMap O S) (I ^ k) → Nm x - Nm y ∈ Ideal.map (algebraMap O S) (I ^ k)) → t - Nm (P₁ : S) ∈ Q 1 → (∀ m, 1 ≤ m → ∀ P : Sˣ, t - Nm (P : S) ∈ Q m → ∃ P' : Sˣ, (P' : S) - (P : S) ∈ Q m ∧ t - Nm (P' : S) ∈ Q (m + 1)) → ∃ L : Sˣ, Nm (L : S) = t := by
  first | exact @GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation | exact GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation | (intros; apply GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation <;> assumption)
