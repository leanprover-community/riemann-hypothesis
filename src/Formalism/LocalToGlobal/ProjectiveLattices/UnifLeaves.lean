import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)


def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩


end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def ClassOcc (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) : Prop :=
  ∀ h : GA D V, ∃ k, ∃ γ ∈ GQ V,
      ((U.X k).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ k (F.t (ik k) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w)

end Genus

section Rows

variable {D : D7}



end Rows

end Formalism.L2.Pj
