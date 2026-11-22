module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def DefQuatExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Even (Module.finrank ℚ F) → Nonempty (DefQuat F)

def CuspSemisimpleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), TR.IsCuspForm φ →
    (∃ s : ℂ, TR.lie F a (TR.oneL F a) φ = s • φ) → φ ∈ ⨆ π : TR.CuspSub F a, π.V

end UpperTheory.V.Published
