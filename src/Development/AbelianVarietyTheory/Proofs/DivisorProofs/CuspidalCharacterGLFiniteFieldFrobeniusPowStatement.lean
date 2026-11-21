import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HcGal

variable {F F' : Type} [Field F] [Field F']

theorem gal_coe (t : F →+* F') {n : ℕ} (x : GL (Fin n) F) :
    ((gal t n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (x : Matrix (Fin n) (Fin n) F).map t := by
  ext i j; simp [gal]

theorem gal_id {n : ℕ} (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem ent_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem isUnit_map_iff (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map t) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have : (M.map t).det = t M.det := by
    rw [RingHom.map_det]; rfl
  rw [this, _root_.map_ne_zero]

theorem toG_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map t) = gal t n (toG M) := by
  unfold toG
  by_cases h : IsUnit M
  · rw [dif_pos h, dif_pos ((isUnit_map_iff t M).2 h)]
    apply Units.ext
    rw [gal_coe, IsUnit.unit_spec, IsUnit.unit_spec]
  · rw [dif_neg h, dif_neg (fun h' => h ((isUnit_map_iff t M).1 h')), map_one]

theorem tlG_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (gal t n x) = gal t a (tlG a x) := by
  unfold tlG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [tl, Matrix.map_apply, ent_map]

theorem brG_gal (t : F →+* F') (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (gal t n x) = gal t b (brG a b x) := by
  unfold brG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [br, Matrix.map_apply, ent_map]

theorem inPar_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (gal t n x) ↔ InPar a x := by
  unfold InPar
  simp only [gal_coe, Matrix.map_apply, map_eq_zero]

theorem gal_bijective (t : F ≃+* F') (n : ℕ) : Function.Bijective (gal (t : F →+* F') n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨gal (t.symm : F' →+* F) n, fun x => ?_, fun x => ?_⟩
  · ext i j; simp [gal]
  · ext i j; simp [gal]

theorem hc_gal : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) =
    hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  intro F _ _ t a b n α β x
  unfold hc hcTw
  congr 1
  symm
  refine finsum_eq_of_bijective (gal (t : F →+* F) n) (gal_bijective t n) fun y => ?_
  rw [gal_id, gal_id, ← map_inv, ← map_mul, ← map_mul, tlG_gal, brG_gal]
  simp only [inPar_gal]

end GlobalTheory.Shin.HcGal
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) = hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  first | (exact @GlobalTheory.Shin.HcGal.hc_gal) | (exact GlobalTheory.Shin.HcGal.hc_gal) | (intros; apply GlobalTheory.Shin.HcGal.hc_gal  <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_gal (F : Type) [Field F] [Finite F] (t : F ≃+* F) (S : F[X] → ℂ) :
    ∀ (n : ℕ) (x : GL (Fin n) F),
      psiG S n (gal (t : F →+* F) n x) = psiG (fun P => S (P.map (t : F →+* F))) n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n (gal (t : F →+* F) n x), GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n x]
    congr 1
    · simp only [chG, gal]
      congr 1
      rw [← Matrix.charpoly_map]
      rfl
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t a (n - a) n]
      have ha' : a < n := Finset.mem_range.1 ha
      congr 1
      funext y
      exact ih a ha' y

theorem cusp_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F),
    cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  intro F _ _ θ t j ht m k x
  simp only [cusp]
  rw [psiG_gal F t]
  congr 2
  funext P
  exact GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (t : F →+* F) j (fun y => ht y) k P

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F), cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  first | (exact @GlobalTheory.Shin.cusp_gal) | (exact GlobalTheory.Shin.cusp_gal) | (intros; apply GlobalTheory.Shin.cusp_gal <;> assumption)
end
