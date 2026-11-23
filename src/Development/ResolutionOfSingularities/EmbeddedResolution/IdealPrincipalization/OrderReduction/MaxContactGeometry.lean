module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupLiftCongruence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReductionCorrectness

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := EmbeddedResolution.blowupLiftEqOnControlledTransform

theorem le_of_support_subset_of_smooth : ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
    ∀ J : X.IdealSheafData,
      (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z :=
  smoothSubschemeIdealIsRadical

theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have : AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

theorem isBalanced_comap_of_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
      [AlgebraicGeometry.LocallyOfFiniteType q],
    IsDerivBalanced T.base T.structMap T.ideal T.mult →
    IsDerivBalanced T.base q (T.ideal.comap h) T.mult := by
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ T.structMap) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
  exact Scheme.IdealSheafData.comap_mono f (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi)

theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled.{u} := by
  intro k _ _ X X₁ p _ _ π Z E hZ hπ _ _ _ A μ hμ hA A₁ hA₁
  have hct : A₁ = controlledTransform π Z A μ hπ hA :=
    eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ hA₁
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA
    (μ - 1) (Nat.sub_le μ 1)
  have hsub : μ - (μ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp only [maxContactIdeal_eq_derivIdealSheafIterate]
  rw [hct]
  exact key

theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms.{u} :=
  existsMaxContactControlledTransforms_of_comapLeControlled maxContactIdealComapLeControlled

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rw [SequenceOfBlowups.projectionToBase_zero]
      exact hx
  | succ n ih =>
      intro hn x hx
      have hn' : n < s.length := hn
      have h1 : (s.transitionMapSucc n).base x ∈ orderAtLeastLocus (s.ideal n) T.mult :=
        OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)
          (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal (n + 1)) T.mult
          (s.ideal_succ n hn') (s.center_order n hn') hx
      have h2 := ih (le_of_lt hn') _ h1
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      exact h2

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x (s.center_order i hi hx)

theorem isStrictPullback_of_isPullback_of_center_nonempty : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
    (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
    (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
      (s.projectionToBase i).base x ∈ Set.range φ.base) →
    IsStrictPullbackBlowupSeq φ s' s := by
  intro X' X φ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty (support_comap_center_nonempty_of_mem_range φ s hne hran)

end OrderReductionCorrectness

end FunctorialResolution.EmbeddedResolution

end
