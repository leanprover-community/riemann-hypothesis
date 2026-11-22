module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)}

theorem hsm (h : IsPlaceOver A w) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) :
    ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (Weil_le_Dec h))) := fun i =>
  (ho i).preimage (continuous_inclusion (Ine_le_Dec A))

abbrev xOf (h : IsPlaceOver A w) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) : WD h :=
  WD.mk (WDRep.ofChars h _ (hsm h χ ho))

def Cond (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h) {n : ℕ} (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) (π : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  (rc (IrrGL.of π.ρ π.smooth π.irred)).mono0 ∧ ∀ s : ↥(Ine (F := E) A),
    (rc (IrrGL.of π.ρ π.smooth π.irred)).charPol (ineIncl h s) = (xOf h χ ho).charPol (ineIncl h s)

end UpperTheory.NonzeroTypeTheory
