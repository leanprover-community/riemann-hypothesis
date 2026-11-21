import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameRedEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle

noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

def latV (Λ : Submodule (𝓞 E) (Fin S.rank → E)) : Submodule (𝓞 E) S.V :=
  Λ.comap ((S.frame.equivFun.restrictScalars (𝓞 E) : S.V ≃ₗ[𝓞 E] (Fin S.rank → E)) : S.V →ₗ[𝓞 E] _)

def matOf (s : S.V ≃ₗ[E] S.V) : Matrix (Fin S.rank) (Fin S.rank) E :=
  LinearMap.toMatrix S.frame S.frame (s : S.V →ₗ[E] S.V)

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}


theorem mem_latV (x : S.V) : x ∈ latV S Λ ↔ co S x ∈ Λ := Iff.rfl

theorem B_eq (x y : S.V) : (ofHSpace S).B x y = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [ofHSpace_B, hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl


theorem coMat_mulVec {m : ℕ} (x : Fin m → S.V) (c : Fin m → E) : coMat S x *ᵥ c = co S (∑ a, c a • x a) := by
  ext i
  simp [coMat, co, Matrix.mulVec, dotProduct, mul_comm]

def flagOf (h : IsFrame (starRingEnd E) S.gram T A) (hT : T ≠ 0) : FlagD (ofHSpace S) r :=
  have k (a b : Fin (r + 1)) : (ofHSpace S).B (S.frame.equivFun.symm fun i => A i a)
      (S.frame.equivFun.symm fun i => A i b) = TF r T b a := by
    rw [B_eq, co, co, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← h.2, pairM, Matrix.mul_assoc]
    rfl
  { e := fun a => S.frame.equivFun.symm fun i => A i a
    T := T
    indep := by
      refine LinearIndependent.comp (v := fun a : Fin (r + 1) => S.frame.equivFun.symm fun i => A i a) ?_ _
        (Fin.castSucc_injective r)
      refine LinearIndependent.map' (v := A.col) ?_ _ S.frame.equivFun.symm.ker
      obtain ⟨L, hL⟩ := h.1
      refine Matrix.mulVec_injective_iff.1 fun c d e => ?_
      simpa [Matrix.mulVec_mulVec, hL] using congrArg (L *ᵥ ·) e
    iso := fun a b => by simp only [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
    zperp := fun a => by simp only [k]; simp [TF, Matrix.diagonal_apply, (Fin.castSucc_ne_last a).symm]
    zz := by simp only [k]; simp [TF]
    hT := hT }

end GlobalTheory.IntPair

end
