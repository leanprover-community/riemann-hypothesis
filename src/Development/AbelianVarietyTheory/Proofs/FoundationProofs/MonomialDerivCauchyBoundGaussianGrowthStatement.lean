module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  first | exact @GlobalTheory.GaussCauchy.monomial_deriv_bound | exact GlobalTheory.GaussCauchy.monomial_deriv_bound | (intros; apply GlobalTheory.GaussCauchy.monomial_deriv_bound <;> assumption)
