import Mathlib
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.ProjCW

open Formalism.BasicNotions NumberField IsDedekindDomain

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]



theorem span_pow_smul (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (N : Submodule (𝓞 K) V) :
    Submodule.span K ((((w.asIdeal ^ F) • N : Submodule (𝓞 K) V)) : Set V) =
      Submodule.span K (N : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right (I := w.asIdeal ^ F) (N := N))
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hbF : b ^ F ∈ w.asIdeal ^ F := Ideal.pow_mem_pow hb F
    have hbF0 : (algebraMap (𝓞 K) K (b ^ F)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact pow_ne_zero F hb0
    rw [Submodule.span_le]
    intro n hn
    have h1 : (b ^ F) • n ∈ ((w.asIdeal ^ F) • N : Submodule (𝓞 K) V) := Submodule.smul_mem_smul hbF hn
    have h2 : n = (algebraMap (𝓞 K) K (b ^ F))⁻¹ • ((algebraMap (𝓞 K) K (b ^ F)) • n) := by
      rw [smul_smul, inv_mul_cancel₀ hbF0, one_smul]
    rw [SetLike.mem_coe, h2, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)


end General


end PI.Dv.ProjCW
