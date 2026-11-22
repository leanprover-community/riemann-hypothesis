module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open _root_.Formalism.L2.Col

attribute [local instance] GlobalTheory.Mem.Col2.starE

end GlobalTheory.LvT.Built.TrueLaws
