import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def intS : Subring D.host.E := (integralClosure ℤ D.host.E).toSubring

theorem coe_mem_intS (c : 𝓞 D.host.E) : (c : D.host.E) ∈ intS D := c.isIntegral_coe

def IntM {N : ℕ} (Z : Matrix (Fin N) (Fin N) D.host.E) : Prop := ∀ a b, Z a b ∈ intS D



end Formalism.MainNotions.S.Pv.HH

end
