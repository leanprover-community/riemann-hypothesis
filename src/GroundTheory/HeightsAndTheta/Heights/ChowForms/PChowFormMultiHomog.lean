module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem chowFormMultiHomog : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP

end GroundTheory.Heights₂.Heights
