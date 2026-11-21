import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIsIntegral
import BuildAid.ForwardExisting

section
open NumberField

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_span_eq_top (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (h : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_smul_mem_of_spanning_numberField_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)), Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ v : Fin r → E, ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  atlas_forward_decl GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top
