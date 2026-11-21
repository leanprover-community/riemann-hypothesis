import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow

section
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.single_inv_mul_groupRingSumOverUnitsInv :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (R Γ : Type) [CommRing R] [Group Γ] (φ : (ZMod M)ˣ →* Γ) (c : R)
      (f : ZMod M → R),
      MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ c * sumEl φ f = sumEl φ fun b => c * f (yCl a b) := by
  intro M a _ ha R Γ _ _ φ c f
  unfold sumEl yCl
  rw [Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M) := by
    rw [mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]
  rw [MonoidAlgebra.single_mul_single]
  simp only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]
end

section
open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.twistedStickelbergerElements_agree :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (Γ : Type) [CommGroup Γ] (φ : (ZMod M)ˣ →* Γ) (k : ℕ),
      B4.yEl k a ha φ = Stk.yForm k a φ ∧ B4.ytEl k a φ = Stk.ytEl k a φ ∧ B4.xEl a φ = Stk.xEl a φ ∧
      B4.coefMap ℚ Γ = Stk.cf ℚ Γ := by
  intro M a _ ha Γ _ φ k
  refine ⟨?_, rfl, rfl, ?_⟩
  · have e : B4.sumEl φ (B4.Ek M k) = Stk.sumEl φ (Stk.Ev M k) := rfl
    have hneg : ∀ f : ZMod M → ℚ, (Stk.sumEl φ fun b => -f b) = -Stk.sumEl φ f := by
      intro f
      simp [Stk.sumEl, Finset.sum_neg_distrib]
    have hE : Stk.Eva M k a =
        fun b => Stk.Ev M k b + -((a : ℚ) ^ k * Stk.Ev M k (Stk.yCl a b)) := by
      funext b
      simp [Stk.Eva, sub_eq_add_neg]
    simp only [B4.yEl, B4.thetaEl]
    rw [e, sub_mul, one_mul, mul_neg, Stk.single_inv_mul_groupRingSumOverUnitsInv, Stk.yForm, hE, Stk.sumEl_add, hneg]
    abel
  · apply MonoidAlgebra.ringHom_ext
    · intro n
      simp [B4.coefMap_single]
    · intro g
      simp [B4.coefMap_single]
end
