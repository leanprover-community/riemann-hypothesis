module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
