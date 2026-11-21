import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

section
namespace GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues

theorem rootsOfUnity_inj {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ}
    (hM : (M : k) ≠ 0) {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (hf : f x = f y) : x = y := by
  have key : ∀ z : O, z ^ M = 1 → f z = 1 → z = 1 := by
    intro z hz hfz
    have h := geom_sum_mul z M
    rw [hz, sub_self] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exfalso
      apply hM
      have h2 := congrArg f h1
      simpa [map_sum, map_pow, hfz] using h2
    · exact sub_eq_zero.mp h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
  have hsub : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.pos_of_ne_zero hM0)
  have hyM : y ^ (M - 1) * y = 1 := by rw [← pow_succ, hsub, hy]
  have hz : (x * y ^ (M - 1)) ^ M = 1 := by
    rw [mul_pow, hx, ← pow_mul, mul_comm (M - 1) M, pow_mul, hy, one_pow, one_mul]
  have hfz : f (x * y ^ (M - 1)) = 1 := by
    rw [map_mul, map_pow, hf, ← pow_succ', hsub, ← map_pow, hy, map_one]
  have h1 := key _ hz hfz
  calc x = x * (y ^ (M - 1) * y) := by rw [hyM, mul_one]
    _ = (x * y ^ (M - 1)) * y := by ring
    _ = y := by rw [h1, one_mul]

theorem main : ∀ {O k : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field k] (f : O →+* k) {M : ℕ},
    (↑M : k) ≠ (0 : k) → ∀ {x y : O}, x ^ M = (1 : O) → y ^ M = (1 : O) →
      (f : O → k) x = (f : O → k) y → x = y :=
  fun f _ hM _ _ hx hy hf => rootsOfUnity_inj f hM hx hy hf

end GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
end

section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.TameRed

theorem part_spec {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a M : ℕ, M ≠ 0 ∧ M.Coprime l ∧ Formalism.CyclotomicNorms.primeToPart l x ^ M = 1 ∧
      Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, M, hM0, hcop, ?_, ?_⟩
  · rw [hz, pow_mul, ← pow_mul _ u, mul_comm u, pow_mul, hone, one_pow]
  · rw [hz, ← pow_mul, mul_comm, pow_mul]
    have := pow_eq_pow_of_modEq hmod hone
    rwa [pow_one] at this

theorem eq_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ} (hM : (M : k) ≠ 0)
    {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (h : f x = f y) : x = y := by
  first
  | (rename_i h_2 h_3 h_4; revert O k h_2 h_3 h_4 f M hM x y hx hy h; exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main)
  | exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main ..)

end GlobalTheory.TameRed
end
