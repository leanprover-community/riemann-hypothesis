module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace MUcSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothRepConj_smooth_of {P : Ideal (MRing ι)} {A Z : HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact TopNPoly.smoothRep_smooth_of ha hZ hh

end MUcSmooth

end GroundTheory.Heights₂.Heights.NineStatements
