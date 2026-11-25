module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryComponentsInOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  intro h
  have := hV.isNoetherian
  have := FunctorialResolution.Blowup.noetherianSpace_subscheme (T.boundary.get ⟨j, hj⟩)
  have hnsU : TopologicalSpace.NoetherianSpace
      ↥((boundaryComponentsInOrderLocusOpens T j hj h).toScheme) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(boundaryComponentsInOrderLocus T j hj))
  have hqc : AlgebraicGeometry.QuasiCompact
      ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hclosed : IsClosed (boundaryComponentsInOrderLocus T j hj) :=
    TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset _ _
  have hinj : Function.Injective ⇑(T.boundary.get ⟨j, hj⟩).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).injective
  have himg : IsClosed (⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj) :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).isClosedMap _ hclosed
  have hU : Set.range ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι = boundaryComponentsInOrderLocus T j hj :=
    Scheme.Opens.range_ι _
  have hcomp : ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
      = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ∘ ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι := by
    funext x
    simp
  have hrange :
      Set.range ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
        = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, Set.range_comp, hU]
  have hsupp : ((AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme)
      = closure (Set.range
          ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [hsupp, hrange, himg.closure_eq]
  exact Set.preimage_image_eq _ hinj

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
