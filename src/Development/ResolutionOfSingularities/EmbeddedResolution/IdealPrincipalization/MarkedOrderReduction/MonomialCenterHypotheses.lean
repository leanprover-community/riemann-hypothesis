module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentCodimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
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
import Mathlib.SetTheory.ZFC.PSet
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

namespace MonomialCenterCase

structure MonomialCenterHypotheses : Prop where
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            AlgebraicGeometry.Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ x' : ↥X',
                  ∃ (U' : X'.Opens) (ε : ℕ),
                    x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                        (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)
                          ⊆ (D.support : Set ↥T.scheme)) ∧
                      (D.comap π).comap U'.ι =
                        (Blowup.strictTransform π Z D).comap U'.ι *
                          (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ i : Fin T.boundary.length,
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ

theorem monomialCaseHypotheses_of_monomialCenterHypotheses (h : MonomialCenterHypotheses.{u}) :
    MonomialCaseHypotheses.{u} := by
  exact {
    card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
    center_smooth := h.center_smooth
    center_snc := h.center_snc
    blowup_total_transform := h.blowup_total_transform
    components_subset_divisor_iff := h.components_subset_divisor_iff
    transformed_components := h.transformed_components
    stratum_smooth := MonomialChart.smooth_intersectionIdeal_subscheme
    orderAt_comap_off_exceptional := fun T hT X' π Z hπ x' hx' A =>
      orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A
    orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one }

end MonomialCenterCase

namespace StrictTransformCase

structure StrictTransformHypotheses : Prop extends MonomialCenterCase.MonomialCenterHypotheses.{u} where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_residualHypotheses (h : StrictTransformHypotheses.{u}) :
    StrictTransformAndMonomialCaseHypotheses.{u} := by
  exact {
    strictTransform_components := h.strictTransform_components
    monomial := MonomialCenterCase.monomialCaseHypotheses_of_monomialCenterHypotheses
      h.toMonomialCenterHypotheses }

end StrictTransformCase

end FunctorialResolution.EmbeddedResolution
