import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
import BuildAid.ForwardExisting

section
open IsLocalRing

namespace GlobalTheory

theorem isAdicComplete_of_le_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R →
        IsAdicComplete I R := by
  intro R _ _ _ hm I hI
  exact isAdicComplete_of_le_of_isNoetherianRing R I (maximalIdeal R) hI hm

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  atlas_forward_decl GlobalTheory.isAdicComplete_of_le_maximalIdeal
