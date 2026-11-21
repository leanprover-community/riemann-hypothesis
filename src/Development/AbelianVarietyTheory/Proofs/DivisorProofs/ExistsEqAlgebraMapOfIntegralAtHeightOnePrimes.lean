import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegKrull
import BuildAid.ForwardExisting

section
open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
end

open scoped BigOperators Matrix ComplexConjugate
open Polynomial
theorem _root_.GlobalTheory.T.exists_eq_algebraMap_of_integral_at_height_one_primes : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (t : FractionRing R), (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧ t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) → ∃ a : R, algebraMap R (FractionRing R) a = t := by
  atlas_forward_decl GlobalTheory.integral_of_forall_height_one
