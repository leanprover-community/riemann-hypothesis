import Mathlib
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.BehrendSets.TranslateMean
import Formalism.BehrendSets.FinalE

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

namespace PfM

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

theorem orbitsInt : OrbitsInt := by
  intro e φ hφ
  have hp : ∀ g : GG e, (placeOf g).2 = g.2 ∧ (placeOf g).1 = (g.1.1 * g.1.2, 1) := by
    intro g
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨by simp [placeOf, hg], ?_⟩
      ext <;> simp [placeOf, hg]
    · refine ⟨by simp [placeOf, hg, cc], ?_⟩
      ext <;> simp [placeOf, hg, cc, c0]
  have hsq : ∀ x : ℤˣ, ∀ i : ℤ, x ^ i = if Even i then 1 else x := by
    intro x i
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · simp [zpow_mul, Int.units_sq]
    · have : ¬ Even (2 * k + 1) := by simp
      simp [zpow_add, zpow_mul, Int.units_sq]
  refine ⟨⟨?_, rfl, ?_, orderOf_inv φ⟩, ?_⟩
  · rcases hφ with h | h <;> rw [Prod.fst_inv, h] <;> ext <;> simp [c0]
  · rw [Prod.snd_inv, orderOf_inv]
  · intro τ i
    have h2 : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_Psi_iff, mem_Psi_iff]
      have : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [this, h2, hsq]
      rcases Int.units_eq_one_or τ.1.2 with ht | ht <;> by_cases hi : Even i <;> simp [ht, hi]
    · rw [(hp _).1]; simp
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, c0]
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, sg]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField Ideal


end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

theorem coord {e : ℕ} (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (φ τ : GG e)
    (hφ : φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (i : ℤ) :
    Multiplicative.toAdd (ι (placeOf (φ ^ i * τ)).2) =
      Multiplicative.toAdd (ι τ.2) + i • Multiplicative.toAdd (ι φ.2) := by
  rw [((orbitsInt e φ hφ).2 τ i).2.1, map_mul, map_zpow, toAdd_mul, toAdd_zpow, add_comm]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped TensorProduct


end

end PfM

open Formalism.FrobeniusOrbits


end Formalism.HermitianLattices.FiltrationBoundaryCriterion
