module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentDualFrobeniusOfBlock
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.isNilpotent_dualFrobenius_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  first | exact @GlobalTheory.DualFrobNilMat.isNil_of_block | exact GlobalTheory.DualFrobNilMat.isNil_of_block | (intros; apply GlobalTheory.DualFrobNilMat.isNil_of_block <;> assumption)
