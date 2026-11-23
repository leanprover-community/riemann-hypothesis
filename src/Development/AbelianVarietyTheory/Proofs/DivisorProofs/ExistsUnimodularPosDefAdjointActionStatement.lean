module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointAction
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


theorem _root_.GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m → B0.transpose = B0 → (B0.map (Int.cast : ℤ → ℝ)).PosDef → (∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) → ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧ ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  first | exact @GlobalTheory.exists_unimodular_posDef_adjoint_action | exact GlobalTheory.exists_unimodular_posDef_adjoint_action | (intros; apply GlobalTheory.exists_unimodular_posDef_adjoint_action <;> assumption)
