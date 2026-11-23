module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C}
    [MonObj M] [MonObj N] [IsCommMonObj N] (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M where
  mul_comm := by
    rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm N]

theorem isAbelianScheme_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G]
    [GrpObj (Over.mk (pullback.snd G.hom f))] (φ : pullback G.hom f ⟶ G.left)
    (h : IsGrpPullback (Over.mk (pullback.snd G.hom f)) G f φ) (hG : IsAbelianScheme G) :
    IsAbelianScheme (Over.mk (pullback.snd G.hom f)) := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  refine ⟨isCommMonObj_of_iso e, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd G.hom f); infer_instance
  · show IsProper (pullback.snd G.hom f); infer_instance
  · show GeometricallyConnected (pullback.snd G.hom f); infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
