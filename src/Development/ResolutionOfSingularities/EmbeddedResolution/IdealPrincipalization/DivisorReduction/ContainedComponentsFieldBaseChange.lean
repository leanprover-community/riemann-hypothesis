module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
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

theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary (T.withBoundary E').boundary T.boundary := hBE.symm
  have h := hvbr (T.withBoundary E') T.boundary hV hBE'
  have he : (T.withBoundary E').withBoundary T.boundary = T := MarkedIdealWithBoundary.withBoundary_self T
  rwa [he] at h

private theorem containedComponentsIdeal_withBoundary_of_get_eq (S : MarkedIdealWithBoundary.{u})
    (E' : List S.scheme.IdealSheafData) (j : ℕ) (hjE : j < E'.length)
    (hj : j < S.boundary.length)
    (hget : E'.get ⟨j, hjE⟩ = S.boundary.get ⟨j, hj⟩) :
    DivisorReduction.containedComponentsIdeal (S.withBoundary E') j hjE = DivisorReduction.containedComponentsIdeal S j hj := by
  rw [DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (S.withBoundary E') j hjE,
    DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj]
  exact congrArg (fun D => DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult D) hget

private theorem lowerIdealWithoutBlowup_eq_ideal (S : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  simp [Scheme.IdealSheafData.comap_id]

theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hVb : (T.baseChange K f).IsAdmissible :=
    isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    rw [List.length_take, List.length_take] at h
    omega
  have hget : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  rw [containedComponentsIdeal_withBoundary_of_get_eq (T.baseChange K f) E' j hjE hj' hget]
  exact hfacts.preIdeal_baseChange T hV K f hVb j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal, lowerIdealWithoutBlowup_eq_ideal, MarkedIdealWithBoundary.withBoundary_ideal]
  exact MarkedIdealWithBoundary.baseChange_ideal T K f

end FunctorialResolution.EmbeddedResolution
