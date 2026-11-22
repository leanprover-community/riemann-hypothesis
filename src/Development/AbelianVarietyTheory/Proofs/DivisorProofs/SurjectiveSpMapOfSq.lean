module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

end GlobalTheory.PtExt
