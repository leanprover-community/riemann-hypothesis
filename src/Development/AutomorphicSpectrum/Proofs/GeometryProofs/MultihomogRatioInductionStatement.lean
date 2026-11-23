module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInduction
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

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_ratio_induction : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  exact @GlobalTheory.CompanionTheory.Ar.TwistLine.finite_pairs_common_bidegree
