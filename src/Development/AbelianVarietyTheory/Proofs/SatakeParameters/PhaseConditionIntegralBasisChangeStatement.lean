module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChange
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


theorem _root_.GlobalTheory.T.phaseCondition_integral_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  first | exact @GlobalTheory.phaseCondition_basisChange | exact GlobalTheory.phaseCondition_basisChange | (intros; apply GlobalTheory.phaseCondition_basisChange <;> assumption)
