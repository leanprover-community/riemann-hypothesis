module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def DegreeGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral P (pot L) (fun _ => 1) =
        NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun j => (L j).a)

end

end GroundTheory.Heights₂.Heights.Inter
