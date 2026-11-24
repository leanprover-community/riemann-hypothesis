module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
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

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

theorem IsComponentCompatiblePullback.of_flat (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (hord : ∀ (A : T.scheme.IdealSheafData) (y : ↥Y), orderAt (A.comap g) y = orderAt A (g y)) :
    IsComponentCompatiblePullback T Y k' q g :=
  ⟨fun J 𝒞 h𝒞 hop => hGeom.flat_comap_center T hT Y k' q g hT' J 𝒞 h𝒞 hop,
    fun J => hGeom.flat_components_down T hT Y k' q g hT' J,
    fun J => hGeom.flat_components_up T hT Y k' q g hT' J, hord⟩

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
