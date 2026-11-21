import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.mem_hat_iff_forall_loc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  intro F E _ _ _ _ _ n L hL x
  haveI := hL.1
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff L x
end

section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  first | exact @GlobalTheory.St.G.mem_hat_iff_forall_loc | exact GlobalTheory.St.G.mem_hat_iff_forall_loc | (intros; apply GlobalTheory.St.G.mem_hat_iff_forall_loc <;> assumption)
end
