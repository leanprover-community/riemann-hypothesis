import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DetChrOf

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace Formalism.L2.Col

namespace DetChrOf

section Pull

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]

def chiPull (σ : E →ₐ[F] E) (c : Formalism.L2.DIV.Chr F E K) : Formalism.L2.DIV.Chr F E K := c.comp (Formalism.L2.DIV.h90 σ)

end Pull

section Comparison₂

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


end Comparison₂

section Amb

open Formalism.L2.Ker

variable {D : D7} {X : Fields} (s : Seam D X)

end Amb

end DetChrOf

end Formalism.L2.Col
