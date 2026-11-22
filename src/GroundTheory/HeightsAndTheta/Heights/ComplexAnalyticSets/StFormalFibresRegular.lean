module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegular.Statement : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A], Algebra.FiniteType k A →
    ∀ (m : Ideal A), m.IsMaximal → ∀ (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing A P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
