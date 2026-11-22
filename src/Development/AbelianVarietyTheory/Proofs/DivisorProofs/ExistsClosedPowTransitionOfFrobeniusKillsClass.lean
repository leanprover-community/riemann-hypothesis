module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FrobKill

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}}
  {s : X ⟶ Sp R}

abbrev tU (s : X ⟶ Sp R) (U : AffOp X) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop)

include hR in
theorem cast_sec (U : X.Opens) : (p : Sec s U) = 0 := by
  rw [← map_natCast (algebraMap R (Sec s U)), hR, map_zero]

abbrev resHom (s : X ⟶ Sp R) {U V : AffOp X} (a : U ⟶ V) : tU s U ⟶ tU s V :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := tU s V) (Sec.res s (leOfHom a.unop))
    (affPt_res s (leOfHom a.unop))

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta (U : AffOp X) : tU s U ⟶ h.obj (tU s U) :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := h.obj (tU s U))
    { frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) with
      commutes' := fun r ↦ by
        show frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) (algebraMap R (Sec s U.unop.1) r) = _
        rw [frobR_apply]
        change _ = algebraMap R (Sec s U.unop.1) (frobR p R hR r)
        rw [frobR_apply, map_pow] }
    (by
      have h0 : (p : Γ(Sp (Sec s U.unop.1), ⊤)) = 0 :=
        GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_sec p hR U.unop.1)
      change spMap (frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1)) ≫ affPt s U.unop =
        affPt s U.unop ≫ GlobalTheory.VB.frob X p hX
      rw [← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX _ h0])

theorem eta_φ (U : AffOp X) (b : Sec s U.unop.1) : (eta p hR h U).φ b = b ^ p :=
  frobR_apply p _ (cast_sec p hR U.unop.1) b

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

end GlobalTheory.CechDR.FrobKill
