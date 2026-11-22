module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.Eis

end GlobalTheory.Published

end
