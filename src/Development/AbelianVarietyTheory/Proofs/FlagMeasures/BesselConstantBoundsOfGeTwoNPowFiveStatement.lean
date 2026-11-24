module

public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFive
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  first | exact @GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | exact GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | (intros; apply GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five <;> assumption)
