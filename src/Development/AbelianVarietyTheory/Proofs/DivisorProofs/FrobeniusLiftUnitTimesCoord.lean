import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.frobenius_lift_unit_times_coord : ∀ (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt) (F : Kt →+* Kt) (v v' t : Kt), (p : Kt) * p = 0 → v' ∈ At → v * v' = 1 → (∃ w ∈ At, F v = v ^ p + p * w) → F t = t ^ p → ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  atlas_forward_decl _root_.GlobalTheory.DI.unit_mul_logarithmic_lift
