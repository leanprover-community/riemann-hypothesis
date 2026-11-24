module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAdicSumOriginValuesIntegralFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_unit_adic_sum_origin_values_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  first | exact @GlobalTheory.Mum.exists_unit_origin_sum | exact GlobalTheory.Mum.exists_unit_origin_sum | (intros; apply GlobalTheory.Mum.exists_unit_origin_sum <;> assumption)
