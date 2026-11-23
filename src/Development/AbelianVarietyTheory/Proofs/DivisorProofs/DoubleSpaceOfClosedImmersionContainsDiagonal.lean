module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem dbl_of_isClosedImmersion_lift : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  intro F _ Y Z _ p₁ p₂ h hi hη
  have hp₁ : p₁ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.fst Y.str Y.str :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hp₂ : p₂ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.snd Y.str Y.str :=
    (Limits.pullback.lift_snd _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [hp₁, Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _
      (ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver)
  have hc : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ h)) :=
    (Limits.pullback.lift p₁ p₂ h).isClosedEmbedding.isClosed_range
  have hrange : Set.range (Limits.pullback.diagonal Y.str) ⊆ Set.range (Limits.pullback.lift p₁ p₂ h) := by
    rintro _ ⟨y, rfl⟩
    have hs := ((genericPoint_spec Y.X).specializes (Set.mem_univ y)).map
      (Limits.pullback.diagonal Y.str).continuous
    exact hs.mem_closed hc hη
  have hle : (Limits.pullback.lift p₁ p₂ h).ker ≤ (Limits.pullback.diagonal Y.str).ker := by
    refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker _ ⟨_, hc⟩ hrange)
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact (Limits.pullback.lift p₁ p₂ h).range_subset_ker_support
  have hδ := IsClosedImmersion.lift_fac (Limits.pullback.lift p₁ p₂ h) (Limits.pullback.diagonal Y.str) hle
  refine ⟨IsClosedImmersion.lift _ _ hle, ?_, ?_, ?_, ?_⟩
  · have : IsClosedImmersion (IsClosedImmersion.lift _ _ hle ≫ Limits.pullback.lift p₁ p₂ h) := by
      rw [hδ]; infer_instance
    exact IsClosedImmersion.of_comp _ (Limits.pullback.lift p₁ p₂ h)
  · have e₁ := hδ =≫ Limits.pullback.fst Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst] at e₁
  · have e₂ := hδ =≫ Limits.pullback.snd Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd] at e₂
  · intro K _ w hw
    have e : w = (w ≫ p₁) ≫ IsClosedImmersion.lift _ _ hle := by
      rw [← cancel_mono (Limits.pullback.lift p₁ p₂ h), Category.assoc, hδ]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id, hw]
    refine ⟨(w ≫ p₁) (IsLocalRing.closedPoint K), ?_⟩
    have e' := congrArg (fun f : Sp K ⟶ Z => f (IsLocalRing.closedPoint K)) e
    exact e'.symm

end GlobalTheory.FlagPush
