import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem howeUp_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i →
    GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  intro R H what₂ N A i hL hB hS hR σ P P' hP hP'
  refine GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hB hS hR P P' (Filter.Eventually.of_forall fun w hw => ?_)
  rw [hL σ P hP w hw, hL σ P' hP' w hw]

end GlobalTheory.RowTie
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  atlas_forward_decl GlobalTheory.RowTie.howeUp_of_pairLift
