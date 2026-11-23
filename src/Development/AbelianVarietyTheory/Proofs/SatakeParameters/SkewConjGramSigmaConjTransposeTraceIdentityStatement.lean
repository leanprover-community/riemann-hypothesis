module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SkewConjGramSigmaConjTransposeTraceIdentity
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

open Matrix

theorem _root_.GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  first | exact @GlobalTheory.skewConj_cT_mul_and_trace | exact GlobalTheory.skewConj_cT_mul_and_trace | (intros; apply GlobalTheory.skewConj_cT_mul_and_trace <;> assumption)
