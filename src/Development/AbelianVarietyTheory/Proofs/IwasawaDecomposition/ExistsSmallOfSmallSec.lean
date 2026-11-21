import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

namespace GlobalTheory.SmallInduced

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h]
  congr 1
  exact IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_ne_zero {f : Z.functionField} (hf : UnitAt (below y) f) : TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

omit [IsIntegral Z] in

theorem top_le_of_below {U : Z.Opens} (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    TrueGeo.valAt y (fnOf U h a) = valR y U a := by
  rw [← algebraMap_germ hy, valAt_algebraMap, valR, dif_pos (top_le_of_below y hy)]
  have := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  exact this

end Val

theorem valR_spMap_comp {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) {X : Scheme.{0}}
    (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valR (spMap φ ≫ x) U a = φ (valR x U a) := by
  rw [← valR_appLE (spMap φ) x h le_top, valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from le_top), valR, dif_pos h]
  have := congrArg (fun ψ => ψ.hom ((x.appLE U ⊤ h).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  refine Eq.trans ?_ this
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ψ.hom ((x.appLE U ⊤ h).hom a)))
    (Scheme.Hom.appLE_eq_app (spMap φ) (U := ⊤))


end GlobalTheory.SmallInduced
