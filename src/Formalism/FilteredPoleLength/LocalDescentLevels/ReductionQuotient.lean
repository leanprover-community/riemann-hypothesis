import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient
import Formalism.LogFactorialIndices.LogProductFormula

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace BasisReduction

open Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

abbrev q (A B : Submodule O X) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)




theorem q_zero {A B : Submodule O X} (h : A ≤ B) : q A B = 0 := qlen_eq_zero h



end BasisReduction

open BasisReduction


end Formalism.LatticeBaseChangeAlt
