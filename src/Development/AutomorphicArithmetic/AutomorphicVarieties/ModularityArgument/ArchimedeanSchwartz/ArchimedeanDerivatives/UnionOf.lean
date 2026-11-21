import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Inf

section Primes

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]














end Primes

section Main

open Classical in

private def pick {X : Type} (sat : X → Multiset ℂˣ → Prop) (w : X) : Multiset ℂˣ :=
  if h : ∃ B, sat w B then h.choose else 0





end Main

end UpperTheory.V.Z.Inf
