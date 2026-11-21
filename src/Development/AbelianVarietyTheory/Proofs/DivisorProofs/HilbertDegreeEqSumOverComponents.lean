import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ChowHt.Associativity

section Length

variable {A : Type} [CommRing A]



end Length

section LocalLength

variable {R : Type} [CommRing R]



open Classical in

noncomputable def lenAt (I Q : Ideal R) : ℕ :=
  if h : Q.IsPrime then (haveI := h; localLength I Q).toNat else 0




end LocalLength

section Hilbert

variable {k : Type} [Field k] {N : ℕ}

local notation "S" => MvPolynomial (Fin N) k


theorem ringKrullDim_quotient_add_one_le {P I : Ideal S} [P.IsPrime] (h : P < I) :
    ringKrullDim (S ⧸ I) + 1 ≤ ringKrullDim (S ⧸ P) := by
  obtain ⟨a, ha, haP⟩ := SetLike.exists_of_lt h
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk P a)
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ha)


end Hilbert


end GlobalTheory.ChowHt.Associativity
