import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

variable {G : Type*} [Group G]

def ratio (A S : Subgroup G) : ℝ := (A.relIndex S : ℝ) / (S.relIndex A : ℝ)





abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom


end Formalism.L2.SG.Pf.RelativeIndexFlags
