module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.unitaryPQ_continuous_character_eq_det_pow_prod : ∀ (n p q : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 → B' * B = 1 → Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) → s * B = B * Matrix.fromBlocks 1 0 0 (-1) → ∀ c : Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k k' : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → k'ᴴ * G * k' = G → s * k' = k' * s → c (k * k') = c k * c k') → (∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → ‖c k‖ = 1) → ContinuousOn c {k | kᴴ * G * k = G ∧ s * k = k * s} → ∃ x y : ℤ, ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → c k = ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det ^ x * ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det ^ y := by
  first | exact @GlobalTheory.UpqChar.char_Upq | exact GlobalTheory.UpqChar.char_Upq | (intros; apply GlobalTheory.UpqChar.char_Upq <;> assumption)
