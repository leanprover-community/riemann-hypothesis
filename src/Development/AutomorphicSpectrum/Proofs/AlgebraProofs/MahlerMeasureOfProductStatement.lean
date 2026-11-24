module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.mahler_measure_of_product : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow <;> assumption)
