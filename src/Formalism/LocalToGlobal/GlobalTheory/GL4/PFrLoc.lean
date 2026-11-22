module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrCore
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

variable (v : HeightOneSpectrum (𝓞 F))

end Loc

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end Lev

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
