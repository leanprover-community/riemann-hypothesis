module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtComm

theorem isCommMonObj_of_dominant {S S' : Scheme.{0}} {f : S' ⟶ S} [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    [Flat A.hom] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
    [IsCommMonObj A'] : IsCommMonObj A := by
  have := ExtUnique.flat_tensorObj A A
  have key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A),
      t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A] := fun T t => by
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [lift_braiding_hom_assoc]
    exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
      ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))
  refine ⟨?_⟩
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_
  exact congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f))
    (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))

end GlobalTheory.SplitExtComm
