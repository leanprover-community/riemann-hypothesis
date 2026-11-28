module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# A faithful complex character over a finite field

The Teichmüller lifts of the elements of the algebraic closure of a finite field are integral over
`ℤ`. Embedding the ring they generate into `ℂ` gives an injective multiplicative character.
Green's characters use a fixed choice of this character.
-/

@[expose] public section

noncomputable section

namespace New

open Function

variable (k : Type*) [Field k] [Finite k]

/-- A chosen injective multiplicative character from the algebraic closure of `k` to `ℂ`
(arbitrary if there is none). For finite `k` one exists (`New.exists_injective_mulChar`), so the
chosen character is injective (the instance `New.faithfulChar_injective`). -/
def faithfulChar : MulChar (AlgebraicClosure k) ℂ :=
  Classical.epsilon fun T : MulChar (AlgebraicClosure k) ℂ ↦ Injective T

/-- The field K is algebraically closed and the multiplicative character T : K → ℂ is injective,
so it embeds K^× in ℂ^×. -/
class IsFaithfulMulChar (K : Type*) [Field K] (T : outParam (MulChar K ℂ)) :
    Prop extends IsAlgClosed K where
  /-- The character T is injective. -/
  injective : Injective T

open WittVector Algebra IsIntegral RingHom

/-- The algebraic closure of a finite field has an injective multiplicative character to `ℂ`. -/
theorem exists_injective_mulChar (k : Type*) [Field k] [Finite k] :
    ∃ T : MulChar (AlgebraicClosure k) ℂ, Injective T := by
  -- Teichmüller lifts are integral over `ℤ`, and the ring `R` of Witt vectors integral over
  -- `ℤ` is a domain of characteristic zero, so it embeds in `ℂ`.
  have : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have : CharZero (WittVector (ringChar k) (AlgebraicClosure k)) :=
    -- it contains the Witt vectors of the prime field, which are the `p`-adic integers
    (charZero_iff (map_injective _ (ZMod.castHom_injective (AlgebraicClosure k)))).1
      (toPadicInt (ringChar k)).charZero
  let R := integralClosure ℤ (WittVector (ringChar k) (AlgebraicClosure k))
  have h_int (x : AlgebraicClosure k) : teichmuller (ringChar k) x ∈ R := by
    -- `k[x]` is finite, so its monoid algebra is integral over `ℤ`; map it to the Witt vectors.
    have : Finite k[x] :=
      Module.finite_iff_finite.1 (finite_adjoin_simple_of_isIntegral (R := k) (isIntegral x))
    let x' : k[x] := ⟨x, self_mem_adjoin_singleton k x⟩
    let toWitt : MonoidAlgebra ℤ k[x] →ₐ[ℤ] WittVector (ringChar k) (AlgebraicClosure k) :=
      MonoidAlgebra.lift ℤ _ _ ((teichmuller (ringChar k)).domRestrict k[x])
    have h_apply : toWitt (MonoidAlgebra.single x' 1) = teichmuller (ringChar k) x := by
      simp [toWitt, x']
    have h_single : _root_.IsIntegral ℤ (MonoidAlgebra.single x' (1 : ℤ)) := isIntegral _
    rw [← h_apply]
    exact h_single.map toWitt
  let lift : MulChar (AlgebraicClosure k) R :=
    { (teichmuller (ringChar k)).codRestrict R h_int with
      map_nonunit' := by simp [Subtype.ext_iff] }
  let emb : R →ₐ[ℤ] ℂ := IsAlgClosed.lift
  -- The kernel of `emb` is a prime of `R` lying over `(0)`, and `R` is integral over `ℤ`.
  have h_emb : Injective emb :=
    (injective_iff_ker_eq_bot emb).2 (Ideal.eq_bot_of_liesOver_bot ℤ (Ideal.comap emb ⊥))
  refine ⟨lift.ringHomComp emb.toRingHom, fun x y h ↦ ?_⟩
  -- The coefficient `0` of the Teichmüller lift of `x` is `x`.
  have h_lift : lift x = lift y := h_emb h
  have h_coeff : (teichmuller (ringChar k) x).coeff 0 = (teichmuller (ringChar k) y).coeff 0 :=
    congrArg (fun w : R ↦ (w : WittVector (ringChar k) (AlgebraicClosure k)).coeff 0) h_lift
  simpa only [teichmuller_coeff_zero] using h_coeff

/-- For a finite field `k` the character `faithfulChar k`, chosen among the multiplicative
characters from the algebraic closure of `k` to `ℂ`, is injective, so it is faithful
(`IsFaithfulMulChar`). -/
instance faithfulChar_injective {k : Type*} [Field k] [Finite k] :
    IsFaithfulMulChar (AlgebraicClosure k) (faithfulChar k) where
  injective := Classical.epsilon_spec (exists_injective_mulChar k)

end New
