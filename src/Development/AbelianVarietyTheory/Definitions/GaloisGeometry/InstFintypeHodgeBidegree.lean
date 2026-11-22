module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CatH

universe v u v' u'

section Wedge

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def wedgeOm {q q' Q : ℕ} (h : q + q' = Q) : Om R B q →ₗ[R] Om R B q' →ₗ[R] Om R B Q :=
  LinearMap.mk₂ R (fun x y ↦ ⟨x.1 * y.1, h ▸ mul_mem x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

variable {R B}

@[simp] theorem coe_wedgeOm {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    (wedgeOm R B h x y : DR R B) = x * y := rfl

variable (R B) in
def oneOm : Om R B 0 := ⟨1, by
  change _ ∈ LinearMap.range _ ^ 0
  rw [pow_zero]; exact Submodule.one_le.1 le_rfl⟩

end Wedge

section Terms

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

variable {F}

end Terms

section Total

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

instance instFintypeHodgeBidegree (n : ℕ) : Fintype (Bidegree n) :=
  Fintype.subtype (Finset.HasAntidiagonal.antidiagonal n) fun _ ↦
    Finset.HasAntidiagonal.mem_antidiagonal

variable {F}

end Total

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'}
  [Category.{v'} C'] {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  (μ : CoefMap σ F F')

end Pull

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

end Cone

section Scheme

variable {k k' : Type} [CommRing k] [CommRing k'] {X X' : Scheme.{0}}

variable {s : X ⟶ Sp k} {a b n : ℕ}

end Scheme

end GlobalTheory.HodgeCoh
