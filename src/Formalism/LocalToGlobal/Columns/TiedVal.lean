module

public import Formalism.LocalToGlobal.Columns.TiedCls

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatSpanG {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

end Rec

end Formalism.L2.Col
