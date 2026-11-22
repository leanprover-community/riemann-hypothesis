module

public import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Per

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (M : ModelsOf F r)

def LieEig : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ τ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u i P) v → IsEigAt c τ v →
      ∃ a : Fin (Dw.mult τ) → ℂ, IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, a j • eb e τ j) v

end Fam

section Red

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}
  (hTE : ExpTan e F) (hEL : ExpLin e F) (hLE : LieEig e F) (hP : PerAt e F M) (s : GenSec e F M)
  (hs : IsGenSec e F M s)

end Red

section Row

variable {D : D7}

end Row

section Gam

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Gam

section GamL

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}

end GamL

end Formalism.L2.Pj
