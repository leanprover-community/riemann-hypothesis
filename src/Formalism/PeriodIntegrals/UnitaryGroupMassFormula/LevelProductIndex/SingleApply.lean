import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    ∃ (k : ℕ) (m : Fin k → Fin n → E), (∀ i, m i ∈ Lb) ∧
      (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) := by
  have : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  refine ⟨k, fun i => (s i : Fin n → E), fun i => (s i).2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨z, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [Submodule.coe_sum] at h2
  exact h2.symm

theorem prV_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] a v := by
  simp [prV, evalV, Algebra.TensorProduct.map_tmul]
  rfl


def adOf {F : Type} [Field F] [NumberField F] (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  (⟨a, Filter.Eventually.of_forall ha⟩ :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem adOf_apply {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    adOf a ha v = a v := rfl

theorem adOf_mem {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : adOf a ha ∈ intAd F := fun v => ha v


end PI.LPI
end
end

section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) z) = sigR σ (v.adicCompletion F) (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [prV, sigR, evalV, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, evalV, Algebra.TensorProduct.map_tmul]

def single {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F := by
  classical
  exact adOf (Pi.single v a) (fun w => by
    by_cases h : w = v
    · subst h; simpa using ha
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _)

theorem single_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : single v a ha v = a := by
  classical
  simp [single, adOf_apply]



end PI.LPI
end
end
