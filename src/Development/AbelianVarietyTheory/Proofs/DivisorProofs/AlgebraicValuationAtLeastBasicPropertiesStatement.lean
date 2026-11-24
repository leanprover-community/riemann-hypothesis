module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) := by
  first | exact @GlobalTheory.SzRules.main | exact GlobalTheory.SzRules.main | (intros; apply GlobalTheory.SzRules.main <;> assumption)
