module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.DualWeyl MvPolynomial NumberField

theorem _root_.GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ), Antitone la → ∀ f ∈ nabla la K, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la → f = evalAt 1 f • extremal la K := by
  first | exact @GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | exact GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | (intros; apply GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight <;> assumption)
