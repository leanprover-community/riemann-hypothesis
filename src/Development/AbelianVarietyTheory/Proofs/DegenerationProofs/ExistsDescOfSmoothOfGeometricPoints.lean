module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory

theorem exists_desc_of_smooth_of_geometricPoints :
    ∀ (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (X Y : Over (Sp K)), Smooth X.hom → IsSeparated Y.hom → ∀ f : pullback X.hom (spMap (algebraMap K C)) ⟶ Y.left, f ≫ Y.hom = pullback.fst X.hom (spMap (algebraMap K C)) ≫ X.hom → (∀ (F : Type) [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ pullback X.hom (spMap (algebraMap K C))), x ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ → x ≫ f = x' ≫ f) → ∃ f₀ : X ⟶ Y, pullback.fst X.hom (spMap (algebraMap K C)) ≫ f₀.left = f := by
  intro K C _ _ _ _ X Y hX hY f hf H
  have : IsReduced (pullback X.hom (spMap (algebraMap K C))) :=
    isReduced_of_smooth_of_isReduced (pullback.snd X.hom (spMap (algebraMap K C)))
  obtain ⟨ψ, hψ⟩ := ArcDataDescent.exists_desc_of_points (algebraMap K C)
    (IsPullback.of_hasPullback X.hom (spMap (algebraMap K C))) Y.hom f X.hom hf H
  have f₁ : Flat (spMap (algebraMap K C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective (spMap (algebraMap K C)) :=
    ⟨fun y => ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi (pullback.fst X.hom (spMap (algebraMap K C))) := Flat.epi_of_flat_of_surjective _
  refine ⟨Over.homMk ψ ?_, hψ⟩
  rw [← cancel_epi (pullback.fst X.hom (spMap (algebraMap K C))), ← Category.assoc, hψ]
  exact hf

end GlobalTheory
