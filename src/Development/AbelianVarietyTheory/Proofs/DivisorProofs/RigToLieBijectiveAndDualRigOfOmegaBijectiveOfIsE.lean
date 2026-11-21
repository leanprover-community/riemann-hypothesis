import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_invariantDifferentials_of_etale : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  atlas_forward_decl GlobalTheory.PDivGroup.subsingleton_omega_of_isEt
end

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (h : (p : k) = 0)
      (G : PDivGroup p k), G.IsEt →
      Function.Bijective (G.rigToLie h) ∧ Function.Bijective G.dual.rigOfOmega := by
  intro p _ k _ _ _ h G hG
  obtain ⟨h1, h2⟩ := GlobalTheory.T.subsingleton_invariantDifferentials_of_etale p k G hG
  refine ⟨⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, G.rigToLie_surjective h⟩,
    ⟨G.dual.rigOfOmega_injective_of_eq_zero h, fun y => ?_⟩⟩
  · obtain ⟨w, rfl⟩ := (G.exact_rigOfOmega_rigToLie h x).1 hx
    rw [Subsingleton.elim w 0, map_zero]
  · refine (G.dual.exact_rigOfOmega_rigToLie h y).1 ?_
    exact LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end
