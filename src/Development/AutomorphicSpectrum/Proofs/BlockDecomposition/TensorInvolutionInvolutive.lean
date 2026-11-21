import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import BuildAid.ForwardExisting

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem sigR_sigR_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  intro F E _ _ _ _ _ σ h K _ _ t
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.CompanionTheory.SaGen
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_involution_involutive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq
