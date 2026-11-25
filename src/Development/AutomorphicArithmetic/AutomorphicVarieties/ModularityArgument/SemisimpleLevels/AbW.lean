module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne

namespace UpperTheory.V.Lev

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (X - 1) ^ x.lpDim

end UpperTheory.V.Lev

end
