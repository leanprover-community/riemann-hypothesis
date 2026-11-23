module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
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

def HasSmoothCoordCodim {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
    (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
    AlgebraicGeometry.Smooth q ∧
      q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
      restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q

theorem hasSmoothCoordCodim_iff {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) :
    HasSmoothCoordCodim s t c ↔
      ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
        (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
        AlgebraicGeometry.Smooth q ∧
          q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
          restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q :=
  Iff.rfl

end FunctorialResolution.EmbeddedResolution

end
