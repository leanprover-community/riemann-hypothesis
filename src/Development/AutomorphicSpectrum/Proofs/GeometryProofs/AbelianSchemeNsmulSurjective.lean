module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem surjective_pow_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 →
      Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro K _ A _ hA n hn
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hA)
  haveI : IsProper A.hom := IsAbelianScheme.proper (self := hA)
  haveI : GeometricallyConnected A.hom := IsAbelianScheme.geomConnected (self := hA)
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI : ConnectedSpace (Sp K) := inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of K)))
  have hw : ((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  haveI : Flat ((𝟙 A) ^ n : A ⟶ A).left :=
    GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Sp K) A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA) n
      (Nat.one_le_iff_ne_zero.mpr hn)
  haveI : LocallyOfFiniteType ((𝟙 A) ^ n : A ⟶ A).left :=
    HasRingHomProperty.of_comp (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h)
      (by rw [hw]; infer_instance)
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  haveI : LocallyOfFinitePresentation ((𝟙 A) ^ n : A ⟶ A).left := inferInstance
  haveI : UniversallyOpen ((𝟙 A) ^ n : A ⟶ A).left := UniversallyOpen.of_flat _
  haveI : IsProper (((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom) := by rw [hw]; infer_instance
  haveI : IsProper ((𝟙 A) ^ n : A ⟶ A).left := IsProper.of_comp _ A.hom
  haveI : UniversallyOpen A.hom := UniversallyOpen.of_flat _
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have hclopen : IsClopen (Set.range ((𝟙 A) ^ n : A ⟶ A).left) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  refine ⟨fun y => ?_⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hy := Set.mem_range_self (f := ⇑((𝟙 A) ^ n : A ⟶ A).left) y
    rw [h] at hy
    exact hy.elim
  · have hy : y ∈ Set.range ⇑((𝟙 A) ^ n : A ⟶ A).left := by rw [h]; trivial
    exact hy

end GlobalTheory.CompanionTheory.Ar.Approx
