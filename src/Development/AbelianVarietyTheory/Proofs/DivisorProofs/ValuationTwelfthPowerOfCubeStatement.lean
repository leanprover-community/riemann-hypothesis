module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCube
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_valuation_pow_twelve_mul_eq : ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 → D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D → Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) → ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9) = V.valuation D := by
  first | exact @GlobalTheory.valuation_twelfth_power_of_cube | exact GlobalTheory.valuation_twelfth_power_of_cube | (intros; apply GlobalTheory.valuation_twelfth_power_of_cube <;> assumption)
