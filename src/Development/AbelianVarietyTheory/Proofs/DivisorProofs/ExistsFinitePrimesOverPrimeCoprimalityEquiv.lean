import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupEqTopOfLeMaximal
import BuildAid.ForwardExisting

section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.PrimesOverL

theorem primes_over_l : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  first
  | exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | (apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)

end GlobalTheory.PrimesOverL
end

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_primes_over_prime_coprimality_equiv : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  atlas_forward_decl GlobalTheory.PrimesOverL.primes_over_l
