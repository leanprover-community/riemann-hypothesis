module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
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

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_ideal_le_mult_along_sequence (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (s : T.SequenceOfBlowups) :
    ∀ (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) := by
  have : CharZero T.base := hT.charZero
  intro i
  induction i with
  | zero =>
      intro _ x
      have : AlgebraicGeometry.IsOpenImmersion s.toSequenceOfBlowups.isoZero.hom := inferInstance
      rw [s.ideal_zero, orderAt_comap_of_isOpenImmersion]
      exact hord _
  | succ k ih =>
      intro hk x
      have hlt : k < s.toSequenceOfBlowups.length := hk
      have hprev := ih (le_of_lt hlt)
      have hnoeth : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s (k + 1) hk
      have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) := inferInstance
      have hsmooth : AlgebraicGeometry.Smooth (s.projectionToSpec k) :=
        MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s k (le_of_lt hlt)
      have hS : HasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.boundary k) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc k hlt
      have hI : s.ideal k ≤ s.toSequenceOfBlowups.center k ^ T.mult :=
        le_pow_of_hasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.ideal k)
          (s.boundary k) hS T.mult (s.center_order k hlt)
      have hEq : s.ideal (k + 1) =
          controlledTransform (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
            (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI :=
        eq_controlledTransform_of_mul_eq_comap (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
          (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI
          (s.ideal (k + 1)) (s.ideal_succ k hlt)
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le T.base (s.projectionToSpec k)
        (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k) (s.boundary k) hS
        (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) (s.ideal k) T.mult hI hprev x

end FunctorialResolution.EmbeddedResolution
