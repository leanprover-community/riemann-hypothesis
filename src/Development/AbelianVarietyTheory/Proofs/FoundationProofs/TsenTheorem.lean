import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
import BuildAid.ForwardExisting

section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  first | exact @GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | exact GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | (intros; apply GlobalTheory.is_c1_of_finite_of_tsen_lang_systems <;> assumption)
end

section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
  (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n → ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.tsenLang_ratFunc | exact GlobalTheory.tsenLang_ratFunc | (intros; apply GlobalTheory.tsenLang_ratFunc <;> assumption)
end

section
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
end

open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  atlas_forward_decl GlobalTheory.NeedB.tsen
end
