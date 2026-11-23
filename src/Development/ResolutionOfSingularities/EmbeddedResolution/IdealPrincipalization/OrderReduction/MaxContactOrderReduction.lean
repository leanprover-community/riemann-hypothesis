module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificate
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorReduction
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

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isOrderReduction_maxContact_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (hlow : IsMaxOrderReduction Q L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L) :
    IsOrderReduction P (maxContactPrincipalization hinv A) L := by
  refine
    { cert := ?_, base_change := ?_, base_change_strict := ?_, pushforward := ?_,
      order_le := ?_, center_nonempty := ?_, resolves := ?_, smooth_pullback := ?_,
      smooth_pullback_strict := ?_, trivial_of_coSupport_empty := ?_ }
  · intro T hv hdim hO i hi
    exact orderCertificate_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE hV'
      hP' hord
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE
      hV' hP' hord
  · intro T hv hdim hO hbdry hmult Y q e _ hq hsm J hJv hJd hJi
    exact isPushforward_of_isSmoothDivisor hinv P Q A L L' hstar hdes hdiv hlow hdimlink T hv hdim hO
      hbdry hmult Y q e hq hsm J hJv hJd hJi
  · intro T hv hdim hO i hi x
    exact orderAt_ideal_le_mult hinv P A L hdes T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi x
  · intro T hv hdim hO i hi
    exact center_support_nonempty hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO
    exact isResolution_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO)
  · intro T hv hdim hO Y q g _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq E' hBE
      hV' hP' hord
  · intro T hv hdim hO Y q g _ _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq
      E' hBE hV' hP' hord
  · intro T hv hdim hO hemp
    exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) hemp

theorem isOrderReduction_maxContact_dim_le_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hstar : CoverSequenceProperties hinv (fun d => d ≤ n) A)
    (hdes : DescentHypotheses hinv (fun d => d ≤ n) A L) :
    IsOrderReduction (fun d => d ≤ n) (maxContactPrincipalization hinv A) L :=
  isOrderReduction_maxContact_of_descentHypotheses hinv (fun d => d ≤ n) (fun d => d < n) A L L'
    (fun _ _ hab hb => lt_of_lt_of_le hab hb) hlow hdiv hstar hdes

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
