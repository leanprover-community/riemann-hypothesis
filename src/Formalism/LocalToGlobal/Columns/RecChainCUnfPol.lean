module

public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.DGamAut

@[expose] public section

open NumberField IsDedekindDomain Module Matrix MvPolynomial
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

attribute [instance] LevCh.finβ LevCh.decβ

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

end Step

section RhoPt

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end RhoPt

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

variable {W Λ}

end Chain

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

variable (Ξ : XiFamC Λ u)

variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
