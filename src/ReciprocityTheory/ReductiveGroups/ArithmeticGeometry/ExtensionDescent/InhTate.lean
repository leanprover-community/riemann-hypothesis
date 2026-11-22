module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhTate

open Semi Inh

def gv {Y : Scheme.{0}} (a : Γ(Y, ⊤)ˣ) (V : Y.Opens) : Γ(Y, V)ˣ := res le_top a

private theorem map_map_lemma {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U)
    (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE h').op).hom y) =
      (Y.presheaf.map (homOfLE (h.trans h')).op).hom y := by
  first
    | (show ((Y.presheaf.map (homOfLE h').op) ≫ (Y.presheaf.map (homOfLE h).op)).hom y = _; rw [← Functor.map_comp] <;> rfl)
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl)

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(Y, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  exact map_map_lemma h h' _

theorem res_gv {Y : Scheme.{0}} (a : Γ(Y, ⊤)ˣ) {V W : Y.Opens} (h : W ≤ V) :
    res h (gv a V) = gv a W := by
  first
    | exact res_res h le_top a
    | (ext; exact map_map_lemma h le_top _)

def pullTop {X Y : Scheme.{0}} (f : Y ⟶ X) : Γ(X, ⊤)ˣ →* Γ(Y, ⊤)ˣ := Units.map f.appTop.hom

section Ops

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

end Ops

end ReciprocityTheory.ChartRestriction.G.Out.InhTate
