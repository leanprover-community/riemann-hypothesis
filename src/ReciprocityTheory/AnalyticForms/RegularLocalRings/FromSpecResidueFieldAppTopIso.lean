module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.ENatToNat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

def constSec (U : S.Opens) : ℂ →+* Γ(S, U) :=
  (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

def constRes (x : S) : ℂ →+* S.residueField x :=
  (S.evaluation ⊤ x trivial).hom.comp (constSec s ⊤)

open Classical in
def valHom (x : S) : S.residueField x → ℂ := by
  classical
  exact if h : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ then h.choose else fun _ => 0

def val {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) : ℂ :=
  valHom s x (S.evaluation U x hx f)

theorem fromSpecResidueField_appTop_iso (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop, Scheme.evaluation]
  have hid : (Spec (S.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
  simp

theorem constRes_eq (x : S) (hx : IsClosed ({x} : Set S)) [LocallyOfFiniteType s] :
    constRes s x = (residueFieldIsoBase s x hx).inv.hom := by
  have hφ := Scheme.ΓSpecIso_naturality (Spec.preimage (S.fromSpecResidueField x ≫ s))
  rw [Spec.map_preimage] at hφ
  have hpre : Spec.preimage (S.fromSpecResidueField x ≫ s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (S.fromSpecResidueField x ≫ s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField x)).hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have hA : s.appLE ⊤ ⊤ le_top = s.appTop := (s.app_eq_appLE (U := ⊤)).symm
  have hc : constRes s x = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      S.evaluation ⊤ x trivial).hom := rfl
  rw [hc, hA, ← fromSpecResidueField_appTop_iso x]
  show _ = (Spec.preimage (S.fromSpecResidueField x ≫ s)).hom
  rw [hpre, Scheme.Hom.comp_appTop, Category.assoc]

end

end ReciprocityTheory.AnForm.R
