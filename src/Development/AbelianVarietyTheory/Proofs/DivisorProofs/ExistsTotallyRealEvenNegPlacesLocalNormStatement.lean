module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_totallyReal_even_neg_places_local_norm : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | exact @GlobalTheory.NormSign.exists_neg_even_norm_away | exact GlobalTheory.NormSign.exists_neg_even_norm_away | (intros; apply GlobalTheory.NormSign.exists_neg_even_norm_away <;> assumption)
