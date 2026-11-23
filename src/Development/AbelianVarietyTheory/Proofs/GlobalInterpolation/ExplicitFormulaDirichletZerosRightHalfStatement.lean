module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Mathlib.Data.FunLike.Fintype
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaDirichletZerosRightHalf
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.explicit_formula_dirichlet_zeros_right_half : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ u → (zerosBox χ (1 / 2) T).Finite ∧ ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) - (if χ = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u / T + Real.sqrt u * (q : ℝ) ^ 3) * Real.log (q * u * T) ^ 2 := by
  first | exact @GlobalTheory.ExplicitFormulaRight.explicit_formula_right | exact GlobalTheory.ExplicitFormulaRight.explicit_formula_right | (intros; apply GlobalTheory.ExplicitFormulaRight.explicit_formula_right <;> assumption)
