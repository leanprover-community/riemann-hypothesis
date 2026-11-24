module

public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficients
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
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧ ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  first | exact @GlobalTheory.powerSum_second_main | exact GlobalTheory.powerSum_second_main | (intros; apply GlobalTheory.powerSum_second_main <;> assumption)
