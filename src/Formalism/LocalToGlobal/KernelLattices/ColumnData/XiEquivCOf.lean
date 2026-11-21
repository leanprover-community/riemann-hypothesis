import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivOf
import Formalism.LocalToGlobal.Columns.KernelEquivTrivialTuple

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Red

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m) (Am : Amb X) (u : Pr.Word)


end Red

end Formalism.L2.Ker
