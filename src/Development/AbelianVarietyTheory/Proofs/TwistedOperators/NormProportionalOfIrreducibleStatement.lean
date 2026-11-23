module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂), IrrGK M → Module.finrank ℂ ↥(hwSub M.act Λ) = 1 → Function.Injective E₁ → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) → ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  first | exact @GlobalTheory.FockTensor.norm_proportional_of_irreducible | exact GlobalTheory.FockTensor.norm_proportional_of_irreducible | (intros; apply GlobalTheory.FockTensor.norm_proportional_of_irreducible <;> assumption)
