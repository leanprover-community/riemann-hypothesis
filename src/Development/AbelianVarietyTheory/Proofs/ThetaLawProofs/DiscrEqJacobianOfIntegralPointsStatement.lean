module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscrEqJacobianOfIntegralPoints
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_basis_discr_associated_prod_jacobian : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix] [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O)) (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) → (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) → ∃ β : Ix → (MvPowerSeries (Fin g) O), (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧ (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧ Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (F i)).det) := by
  first | exact @GlobalTheory.KeyKa.discr_jacobian_of_points | exact GlobalTheory.KeyKa.discr_jacobian_of_points | (intros; apply GlobalTheory.KeyKa.discr_jacobian_of_points <;> assumption)
