import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem resultant_ne_zero_of_separable_mul :
    ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable →
      resultant P Q ≠ 0 := by
  intro k _ P Q _ _ h
  exact Polynomial.resultant_ne_zero P Q h.isCoprime

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul : ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable → resultant P Q ≠ 0 := by
  atlas_forward_decl GlobalTheory.resultant_ne_zero_of_separable_mul
