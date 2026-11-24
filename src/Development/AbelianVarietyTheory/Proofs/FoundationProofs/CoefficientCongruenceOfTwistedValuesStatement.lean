module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

theorem _root_.GlobalTheory.T.coefficient_congruence_of_twisted_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ), (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → ∀ n, Cg k (F.coeff n) 0 := by
  first | exact @GlobalTheory.KZ.CoefVal.coeff_cg_of_values | exact GlobalTheory.KZ.CoefVal.coeff_cg_of_values | (intros; apply GlobalTheory.KZ.CoefVal.coeff_cg_of_values <;> assumption)
