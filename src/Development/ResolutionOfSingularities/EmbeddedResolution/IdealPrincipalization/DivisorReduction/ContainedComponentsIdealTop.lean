module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hm : T.mult = 1)
    (hlow : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hpush : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hnz : NonzeroOnComponents J := hlow.nonzeroOnComponents
    have hcomap : T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
      rw [hpush]
      exact Blowup.comap_map_of_isClosedImmersion _ J
    have hsub : ∀ y : ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ (T.ideal.support : Set ↥T.scheme) →
        y ∈ (J.support : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      intro y hy
      have h1 := (one_le_orderAt_iff_mem_support T.ideal
        ((T.boundary.get ⟨j, hj⟩).subschemeι y)).mpr hy
      have h2 := orderAt_le_orderAt_comap (T.boundary.get ⟨j, hj⟩).subschemeι T.ideal y
      rw [hcomap] at h2
      exact (one_le_orderAt_iff_mem_support J y).mp (le_trans h1 h2)
    have hempty : divisorComponentsInOrderLocus T j hj = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => ((Set.mem_empty_iff_false x).mp hx).elim⟩
      exfalso
      obtain ⟨C, hCpre, hxC, hCmax⟩ :=
        exists_preirreducible ({x} : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)
          isIrreducible_singleton.2
      have hxC' : x ∈ C := hxC rfl
      have hC : C ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
        ⟨⟨⟨x, hxC'⟩, hCpre⟩, fun u hu hCu => le_of_eq (hCmax u hu.2 hCu)⟩
      refine hnz C hC ?_
      intro y hyC
      have hyc : y ∈ connectedComponent x :=
        hCpre.isPreconnected.subset_connectedComponent hxC' hyC
      have h1 := hx hyc
      rw [hm] at h1
      have h1' : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal 1 := h1
      exact hsub y ((mem_orderAtLeastLocus_one_iff T.ideal _).mp h1')
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩
        (isClosed_divisorComponentsInOrderLocus T hV j hj), Set.image_eq_empty]
    exact hempty
  · exact EmbeddedResolution.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
