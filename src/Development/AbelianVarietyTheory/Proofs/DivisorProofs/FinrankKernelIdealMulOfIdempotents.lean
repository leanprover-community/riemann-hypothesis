import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotentsStatement

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finrank_quot_kerIdeal_mul_of_idem (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0)
    (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) =
      p ^ (n * G.height) := by
  have hdim : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    have h := G.rank_eq n q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    simpa using h
  have hker := GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents p k G u v huv h1 h2 n
  have hord := finrank_eq_ker_mul_range k (G.A n) (G.A n) (u.app n)
  have hr : Module.finrank k (LinearMap.range ((u.app n : G.A n →ₐ[k] G.A n).toLinearMap)) =
      Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) := by
    rw [← hker]
    exact (((u.app n : G.A n →ₐ[k] G.A n).toLinearMap.quotKerEquivRange).symm.finrank_eq).trans rfl
  rw [← hdim, hord, hr]

end GlobalTheory.PDivGroup
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) = p ^ (n * G.height) := by
  atlas_forward_decl GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem
