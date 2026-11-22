module

public import Mathlib
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm

@[expose] public section

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

section Norms

variable {ι n : Type} [Fintype ι] [Fintype n]

variable {h h0 : ι → Matrix n n ℂ}

end Norms

section Calculus

variable {ι : Type} [Fintype ι] {p q : ℕ}

abbrev Pt (ι : Type) (p q : ℕ) : Type := ι → Matrix (Fin p) (Fin q) ℂ

variable {n : Type} [Fintype n] [DecidableEq n]

end Calculus

section Boundary

variable {ι : Type} [Fintype ι] {p q : ℕ}

namespace BdData

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end BdData

end Boundary

end GlobalTheory.HodgeDomain
