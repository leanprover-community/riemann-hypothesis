module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace GlobalTheory.DerivationMemPow

theorem derivation_mem_pow_of_mem_pow_succ {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n := by
  first | exact _root_.GlobalTheory.TriangularityLowCoeff.der_mem_pow | exact @_root_.GlobalTheory.TriangularityLowCoeff.der_mem_pow | apply _root_.GlobalTheory.TriangularityLowCoeff.der_mem_pow <;> assumption

end GlobalTheory.DerivationMemPow
