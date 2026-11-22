module

public import Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}

attribute [local instance] ptYAct

end Pairs

end Formalism.L2.Col
