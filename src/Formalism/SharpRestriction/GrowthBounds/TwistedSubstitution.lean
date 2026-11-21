import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Closed
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ScaleZeroIff
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LogSizeBoundLe
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosDef
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestXiPOfNS
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aMonomial
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem stmtE_of_OpNS (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg : ℝ, RestTSOp D CLa Ck Crk Cdeg ∧ RestNS D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D := by
  obtain ⟨C, _, H⟩ := theorem_II_closed_of_test_bound
  intro CLa Ck Crk Cdeg hA
  exact H D CLa Ck Crk Cdeg hA
    (test_bound_of_two_halves D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60
      (restCloudB_of_op D CLa Ck Crk Cdeg (h CLa Ck Crk Cdeg).1)
      (restFlat_of_Xi D CLa Ck Crk Cdeg C (C + 1) C 26 2 24 60
        (restXi_of_NS D CLa Ck Crk Cdeg 26 2 24 60 (h CLa Ck Crk Cdeg).2)))

theorem stmtE_of_TenNS (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (h : ∀ CLa Ck Crk Cdeg : ℝ, RestNS D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_OpNS D fun CLa Ck Crk Cdeg => ⟨restTSOp_of_ten hT D CLa Ck Crk Cdeg, h CLa Ck Crk Cdeg⟩

end Formalism.MainNotions.TestSideCounting
end
end

section
noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.TestSideCounting

theorem stmtE_of_TenMP (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenNS hT D fun CLa Ck Crk Cdeg => restNS_of D CLa Ck Crk Cdeg 26 2 24 60 (hM _ _ _ _) (hP _ _ _ _)

theorem stmtE_of_MP (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenMP tensor_operators_holds D hM hP

end Formalism.MainNotions.TestSideWords
end
end
