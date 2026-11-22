module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MulMemRiemannRochSpaceAdd

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

end GlobalTheory.Chamber

namespace GlobalTheory.TruncKer

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V)) (μ : Measure (GA D V))

end GlobalTheory.TruncKer

namespace GlobalTheory.Published

end GlobalTheory.Published

end
