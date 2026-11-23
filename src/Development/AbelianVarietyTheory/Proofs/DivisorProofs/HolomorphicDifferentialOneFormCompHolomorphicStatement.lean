module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphic
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

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {c : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}, DifferentiableAt ℝ c (φ v) → DifferentiableAt ℂ φ v → GlobalTheory.CxForm.DelForm.dOne (fun w => c (φ w)) v = GlobalTheory.CxForm.pull (fderiv ℂ φ v) (GlobalTheory.CxForm.DelForm.dOne c (φ v)) := by
  first | exact @GlobalTheory.CxForm.DelForm.dOne_comp_holo | exact GlobalTheory.CxForm.DelForm.dOne_comp_holo | (intros; apply GlobalTheory.CxForm.DelForm.dOne_comp_holo <;> assumption)
