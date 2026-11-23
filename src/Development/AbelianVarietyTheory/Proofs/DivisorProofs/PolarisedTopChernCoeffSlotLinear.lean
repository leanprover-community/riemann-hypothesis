module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmulStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem position_eq_update {n : ℕ} {α : Type} [Zero α] (K₁ L K₀ : α) (j : Fin n) :
    intersection_update_fsHerm_neg_one K₁ L K₀ j = Function.update (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) j L := by
  funext i
  by_cases h : i = j
  · subst h; simp [intersection_update_fsHerm_neg_one]
  · simp [intersection_update_fsHerm_neg_one, Function.update_of_ne h, h]

theorem mixTop_position_linear {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r)
    (s t : ℂ) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  rw [position_eq_update, position_eq_update K₁ L, position_eq_update K₁ L', GlobalTheory.T.polarisedTopChernCoeff_update_add, GlobalTheory.T.polarisedTopChernCoeff_update_smul, GlobalTheory.T.polarisedTopChernCoeff_update_smul]

end GlobalTheory.GoodTop
