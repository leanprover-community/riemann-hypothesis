module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
