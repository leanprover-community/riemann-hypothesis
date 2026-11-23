module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Chart

theorem one_left_spMap {S : Scheme.{0}} (G : Over S) [GrpObj G] {R A : Type} [CommRing R] [CommRing A]
    (x : Sp R ⟶ S) (g : R →+* A) :
    (1 : Over.mk (spMap g ≫ x) ⟶ G).left = spMap g ≫ (1 : Over.mk x ⟶ G).left := by
  let k : Over.mk (spMap g ≫ x) ⟶ Over.mk x := Over.homMk (spMap g) rfl
  have h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]
  rw [h]; rfl

theorem exists_chart_at_point (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V)
      (hUV : U ≤ G.hom ⁻¹ᵁ V),
      RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
      ∃ u : Γ(G.left, U) →+* Localization.Away f,
        (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  let t : Sp R ⟶ G.left := (1 : Over.mk x ⟶ G).left
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let q' : Sp R := q
  obtain ⟨V, hV, hqV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial
  obtain ⟨U, hU, hqU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV
  have hUV' : U ≤ G.hom ⁻¹ᵁ V := hUV
  have hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U} := (t ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen
  refine ⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩
  let a : Sp (Localization.Away f) ⟶ Sp R := spMap (algebraMap R (Localization.Away f))
  have hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    apply hsub
    have : (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at this
    exact this
  let l := IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have hl : spMap (Spec.preimage l).hom = l := by
    simp [spMap]
  rw [one_left_spMap, hl]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.Chart
