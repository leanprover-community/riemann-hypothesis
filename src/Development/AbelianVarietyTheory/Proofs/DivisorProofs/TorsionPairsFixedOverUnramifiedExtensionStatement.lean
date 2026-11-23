module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtension
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

theorem _root_.GlobalTheory.T.torsionPairs_fixed_over_unramified_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  first | exact @GlobalTheory.UnramCharVals.qk_fixed_of_unram | exact GlobalTheory.UnramCharVals.qk_fixed_of_unram | (intros; apply GlobalTheory.UnramCharVals.qk_fixed_of_unram <;> assumption)
