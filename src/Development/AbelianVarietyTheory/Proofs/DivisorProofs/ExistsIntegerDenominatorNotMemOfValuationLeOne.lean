import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
end

open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  atlas_forward_decl GlobalTheory.IntegralDenom.exists_denom_not_mem
