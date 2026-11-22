module

public import Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Dw) in
abbrev LaMod (l : Level H) : Type := Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

def liftLa (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : Dw.La →ₗ[𝓞 E] Dw.La :=
  haveI := Dw.proj
  (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ)
    (Submodule.mkQ_surjective _)).choose

theorem liftLa_spec (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (a : Dw.La) :
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (liftLa γ a) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) := by
  have := Dw.proj
  exact LinearMap.congr_fun (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ) (Submodule.mkQ_surjective _)).choose_spec a

variable (Xo : Moduli Dw l) (c : Coeff l)

def hkScal (cq : c.F) (𝔓 : Ideal (𝓞 E)) (i n : ℕ) : c.F :=
  cq * ((Ideal.absNorm 𝔓 : c.F)⁻¹) ^ (i * n / 2)

end Formalism.L2.Pj
