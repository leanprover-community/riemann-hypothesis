module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

namespace GlobalTheory.AdLat.Model

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.integral_iff (x : F) :
    (∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (h v)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  · rintro ⟨r, rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hv := HeightOneSpectrum.valuation_le_one (K := F) v r
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv
    exact hv

end GlobalTheory.AdLat.Model
