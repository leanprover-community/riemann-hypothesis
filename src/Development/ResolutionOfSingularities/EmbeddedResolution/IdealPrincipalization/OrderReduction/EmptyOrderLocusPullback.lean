module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isPullback_of_orderAtLeastLocus_comap_eq_empty
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (Y : Scheme.{u}) (φ : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth φ]
    (n : SequenceOfBlowups Y) (hn : n.length = 0)
    (hempty : orderAtLeastLocus (T.ideal.comap φ) T.mult = (∅ : Set ↥Y)) :
    IsPullbackBlowupSequence φ n (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have : CharZero T.base := h.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := h.valid.smooth
  refine isPullback_of_length_zero_of_comap_center_eq_top φ n
    (maxContactPrincipalization hinv A T).toSequenceOfBlowups hn ?_
  intro i hi ψ hψ
  refine Blowup.comap_eq_top_of_notMem_support ψ ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.center i) ?_
  intro y hy
  have hmem : ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y)
      ∈ orderAtLeastLocus T.ideal T.mult :=
    OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center T h.valid (maxContactPrincipalization hinv A T) i hi
      (ψ.base y) hy
  have hfy : φ.base y ∈ orderAtLeastLocus T.ideal T.mult := by
    have h1 : φ.base y
        = ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y) := by
      rw [← hψ]
      rfl
    rw [h1]
    exact hmem
  have hcs := orderAtLeastLocus_comap T.base T.structMap φ T.ideal T.mult
  rw [hempty] at hcs
  have hy2 : y ∈ (∅ : Set ↥Y) := by
    rw [hcs]
    exact hfy
  exact hy2.elim

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
