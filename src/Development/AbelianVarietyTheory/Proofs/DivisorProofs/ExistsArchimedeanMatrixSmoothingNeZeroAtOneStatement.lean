module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 → ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | exact GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | (intros; apply GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one <;> assumption)
