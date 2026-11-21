import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLangStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFuncStatement
import BuildAid.ForwardExisting

section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
end

open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  atlas_forward_decl GlobalTheory.NeedB.tsen
