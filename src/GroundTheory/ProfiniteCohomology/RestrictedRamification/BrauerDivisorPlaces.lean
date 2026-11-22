module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MemMaxUnramifiedOutsideOfMemLevelOfField

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal
  FiniteSubfield

noncomputable section

variable {K : GroundTheory.Global.FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

end

end PicInf

end GroundTheory.ProfCoh
