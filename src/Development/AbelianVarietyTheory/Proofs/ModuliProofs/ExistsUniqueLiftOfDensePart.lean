module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isIntegral_of_densePart {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U

theorem existsUnique_lift_of_densePart : ∀ (T U X Y : Scheme.{0}) [IsLocallyNoetherian T] (j : U ⟶ T), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (q : Y ⟶ X) (f : T ⟶ X) (g : U ⟶ Y), IsIntegralHom q → g ≫ q = j ≫ f → ∃! h : T ⟶ Y, j ≫ h = g ∧ h ≫ q = f := by
  intro T U Y Z _ j hT _ _ _ _ p b a _ h
  have := GlobalTheory.IsNormalScheme.of_pred hT
  have H (W : irreducibleComponents T) := by
    have : IsDominant (j ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j› _
    have : IsIntegral (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).toScheme :=
      isIntegral_of_densePart (j ∣_ GlobalTheory.IsNormalScheme.component W)
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ∣_ GlobalTheory.IsNormalScheme.component W)
    exact existsUnique_lift_of_birational (j ∣_ GlobalTheory.IsNormalScheme.component W) p
      ((j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ a) ((GlobalTheory.IsNormalScheme.component W).ι ≫ b)
      (by rw [Category.assoc, h, morphismRestrict_ι_assoc])
  choose c hc _ using H
  obtain ⟨hT⟩ := GlobalTheory.IsNormalScheme.nonempty_isColimit_component (X := T)
  let c₀ : T ⟶ Z := Cofan.IsColimit.desc hT c
  have hc₀ (W) : (GlobalTheory.IsNormalScheme.component W).ι ≫ c₀ = c W := Cofan.IsColimit.fac hT c W
  have h₂ : c₀ ≫ p = b := Cofan.IsColimit.hom_ext hT _ _ fun W ↦ by
    change (GlobalTheory.IsNormalScheme.component W).ι ≫ _ = (GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [reassoc_of% hc₀ W, (hc W).2]
  have h₁ : j ≫ c₀ = a := by
    refine Scheme.Cover.hom_ext (U.openCoverOfIsOpenCover _
      (.comap (GlobalTheory.IsNormalScheme.iSup_component T) j.base.1)) _ _ fun W ↦ ?_
    change (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _ =
      (j ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ _
    rw [← morphismRestrict_ι_assoc, hc₀ W, (hc W).1]
  exact ⟨c₀, ⟨h₁, h₂⟩, fun c' hc' ↦
    lift_unique_of_isDominant j p (hc'.1.trans h₁.symm) (hc'.2.trans h₂.symm)⟩

end GlobalTheory
