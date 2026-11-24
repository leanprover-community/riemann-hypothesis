module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isOpenImmersion_spMap_of_isDiscreteValuationRing (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] :
    IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Tˣ), ?_⟩
    have h1 : algebraMap T K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap T K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

theorem isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem isIso_of_quasiFinite_of_isIso_genericFibre_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      Flat Ga.hom → IsSeparated p.left → LocallyOfFiniteType p.left → QuasiCompact p.left →
      LocallyQuasiFinite p.left → Smooth G.hom → GeometricallyConnected G.hom →
      IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → IsIso p := by
  intro T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have hc : ConnectedSpace ((Over.pullback t).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
  obtain ⟨hG, hN⟩ := isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc
  let q : pullback Ga.hom t ⟶ pullback G.hom t := ((Over.pullback t).map p).left
  have : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))
  have e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left := pullback.lift_fst _ _ _
  have : ConnectedSpace ↥(pullback G.hom t) := hc
  have : IsIntegral (pullback G.hom t) := isIntegral_of_isOpenImmersion (pullback.fst G.hom t)
  have : Nonempty ↥(pullback Ga.hom t) := ⟨inv q (Classical.arbitrary _)⟩
  have : IsIntegral (pullback Ga.hom t) := isIntegral_of_isOpenImmersion q
  have : IsIntegral Ga.left := isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom
  let j := pullback.fst Ga.hom t
  have : IsOpenImmersion (j.opensRange.ι ≫ p.left) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, ← e]
    infer_instance
  have : IsOpenImmersion p.left :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›

end GlobalTheory
