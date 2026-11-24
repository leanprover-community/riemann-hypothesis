module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpow
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

@[expose] public section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ s : ℝ, 1 < s → (classNumber K : ℝ) * Units.regulator K ≤ Real.sqrt |(discr K : ℝ)| ^ s * (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | exact GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow | (intros; apply GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow <;> assumption)
