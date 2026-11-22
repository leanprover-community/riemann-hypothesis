module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

namespace GlobalTheory.CompanionTheory.LsRho

variable {W : Type} [CommRing W]

theorem mapH_eq_self {K : Cx.{1} W} (φ : Cx.Hom K K (RingHom.id W)) (n : ℕ)
    (h : ∀ x, φ.f n x = x) (u : K.H n) : φ.mapH n u = u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_of_comp {K L P : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L P (RingHom.id W))
    (χ : Cx.Hom K P (RingHom.id W)) (n : ℕ) (h : ∀ x, χ.f n x = ψ.f n (φ.f n x)) (u : K.H n) :
    χ.mapH n u = ψ.mapH n (φ.mapH n u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_comp_eq_smul {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L K (RingHom.id W))
    (s : W) (n : ℕ) (h : ∀ x, ψ.f n (φ.f n x) = s • x) (u : K.H n) :
    ψ.mapH n (φ.mapH n u) = s • u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

end GlobalTheory.CompanionTheory.LsRho

end
