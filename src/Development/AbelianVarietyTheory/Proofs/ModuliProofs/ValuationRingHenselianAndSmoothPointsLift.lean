module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem splits_of_monic_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    {f : Polynomial O} (hf : f.Monic) : f.Splits := by
  refine Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K)
    (IsAlgClosed.splits _) fun a ha => ?_
  have hroot : Polynomial.eval₂ (algebraMap O K) a f = 0 := by
    rw [Polynomial.mem_roots (hf.map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map] at ha
    exact ha
  have hint : IsIntegral O a := ⟨f, hf, hroot⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨b, hb⟩

theorem henselianLocalRing_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    HenselianLocalRing O where
  is_henselian f hf a₀ h₁ _ := by
    have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hf
    rw [hs.eval_eq_prod_roots_of_monic hf a₀,
      (IsLocalRing.maximalIdeal.isMaximal O).isPrime.multiset_prod_mem_iff_exists_mem] at h₁
    obtain ⟨c, hc, hcm⟩ := h₁
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨r, (Polynomial.mem_roots hf.ne_zero).mp hr, ?_⟩
    rw [← neg_sub]
    exact neg_mem hcm

theorem isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O]
    [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨g, hg, hdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective p) hp
  have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hgm
  have hd : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hd
  exact ⟨IsLocalRing.residue O r, by rw [← hg, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]⟩

theorem valuationRing_henselian_and_lift_of_isAlgClosed :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  intro O K _ _ _ _ _ _ _
  have := henselianLocalRing_of_valuationRing_of_isAlgClosed O K
  refine ⟨inferInstance, isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O K, ?_⟩
  intro X f hf x hx
  have := hf
  obtain ⟨⟨y, hy⟩, hy'⟩ := reducePoint_residue_surjective f O (𝟙 _) ⟨x, by simpa using hx⟩
  refine ⟨y, hy, ?_⟩
  exact congrArg Subtype.val hy'

end GlobalTheory
