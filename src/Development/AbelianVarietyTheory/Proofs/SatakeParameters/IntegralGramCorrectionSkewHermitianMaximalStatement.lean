module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximal
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

theorem _root_.GlobalTheory.T.integral_gramCorrection_skewHermitian_maximal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  first | exact @GlobalTheory.Hk3.GramSep.eint | exact GlobalTheory.Hk3.GramSep.eint | (intros; apply GlobalTheory.Hk3.GramSep.eint <;> assumption)
