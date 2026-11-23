module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEq
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

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
