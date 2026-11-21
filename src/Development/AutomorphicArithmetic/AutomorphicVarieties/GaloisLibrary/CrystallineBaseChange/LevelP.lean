import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelPS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CompatP

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

open UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}


end UpperTheory.V.Br

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br in
theorem UpperTheory.V.Br.levelP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.LevelP := fun P K _ _ _ hK n hn m hm M hM l _ hl Ω _ _ _ ι r π hL =>
  UpperTheory.V.Lev.levelPS P (UpperTheory.V.Br.compatP P) (UpperTheory.V.Lev.fixedAll P) UpperTheory.V.Lev.unlGap K hK n hn m hm M hM l hl Ω ι r π
    ⟨hL.cont, hL.away, hL.above⟩ hL.safe

end
