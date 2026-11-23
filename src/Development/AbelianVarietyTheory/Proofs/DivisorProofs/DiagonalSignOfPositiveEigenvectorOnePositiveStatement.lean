module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositive
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  first | (exact @GlobalTheory.diag_sign_of_pos_eigenvector) | (exact GlobalTheory.diag_sign_of_pos_eigenvector) | (intros; apply GlobalTheory.diag_sign_of_pos_eigenvector  <;> assumption)
