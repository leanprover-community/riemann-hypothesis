import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.DegOneOfChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.FixedOfCharNeBotIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.LeviInductionForms

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}


end PositivityTheory.LocalParametersCuspidal.DZC

end
