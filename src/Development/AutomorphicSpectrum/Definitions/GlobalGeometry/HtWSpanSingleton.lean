import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem secVal_one {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) : secVal x W h 1 = 1 := by
  simp [secVal]





theorem mem_htW_iff (𝔡 : Ideal O) (q : Cpt ξ) (e : E) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  refine ⟨fun he => ⟨M.mem_eigSp_of_mem_htW L n ρ σ 𝔡 he, ?_⟩, fun h => Submodule.subset_span h⟩
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => intro d _; simp
  | add x y _ _ hx hy => intro d hd; rw [smul_add]; exact Submodule.add_mem _ (hx d hd) (hy d hd)
  | smul c x _ hx =>
    intro d hd
    have : σ d • (c • x) = c • (σ d • x) := by
      show σ d • ((c : Ω) • x) = (c : Ω) • (σ d • x)
      exact smul_comm _ _ _
    rw [this]; exact Submodule.smul_mem _ c (hx d hd)



end GlobalTheory.CompanionTheory.Ar.HtLatCheck
