module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

end IsGal

end GlobalTheory.W1
