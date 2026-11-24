module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshConstNumericalBound
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.cosh_constant_le_exp_three_mul_sq_mul_log : ∀ (p q : ℕ), (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  first | exact @GlobalTheory.CartanInt.cosh_const_numerical_bound | exact GlobalTheory.CartanInt.cosh_const_numerical_bound | (intros; apply GlobalTheory.CartanInt.cosh_const_numerical_bound <;> assumption)
