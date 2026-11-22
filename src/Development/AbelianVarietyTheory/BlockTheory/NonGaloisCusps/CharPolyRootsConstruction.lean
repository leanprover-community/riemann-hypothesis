module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
