module

public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := ∅) (SG := Pr.vGs))

end GenP

section Rec

variable {d : ColDat}

end Rec

end Formalism.L2.Col
