module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinear
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

theorem _root_.GlobalTheory.T.isPeriodMap_comp_injective_realLinear : ∀ {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → Function.Injective R → (∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) → M.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) → (∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) → IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  first | exact @GlobalTheory.PELU.isPeriod_comp_realLinear | exact GlobalTheory.PELU.isPeriod_comp_realLinear | (intros; apply GlobalTheory.PELU.isPeriod_comp_realLinear <;> assumption)
