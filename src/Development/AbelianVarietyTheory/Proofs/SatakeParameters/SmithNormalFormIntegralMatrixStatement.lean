module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.smith_normal_form_integral_matrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ (P P' : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L) (a : Fin n' → ℕ),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ Q * Q' = 1 ∧
      ∀ i j, (P * x * Q - Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.smith_int_approx | exact GlobalTheory.Hk3.smith_int_approx | (intros; apply GlobalTheory.Hk3.smith_int_approx <;> assumption)
