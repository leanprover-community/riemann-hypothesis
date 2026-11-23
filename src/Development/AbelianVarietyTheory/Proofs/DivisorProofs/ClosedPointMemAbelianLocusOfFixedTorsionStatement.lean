module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsion
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  first | exact @GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | exact GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | (intros; apply GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion <;> assumption)
