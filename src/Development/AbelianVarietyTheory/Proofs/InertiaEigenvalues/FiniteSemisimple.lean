import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import BuildAid.ForwardExisting

section
namespace GlobalTheory.PsChar

section Multilinear

variable {R A : Type*} [CommRing A] [Ring R] [Algebra A R]

theorem alt_update_smul_add (T : R →ₗ[A] A) :
    ∀ (n : ℕ) (x : Fin n → R) (i : Fin n) (a : A) (u v : R),
      alt (fun r => T r) n (Function.update x i (a • u + v)) =
        a * alt (fun r => T r) n (Function.update x i u) +
          alt (fun r => T r) n (Function.update x i v)
  | 0, _, i, _, _, _ => i.elim0
  | n + 1, x, i, a, u, v => by
    have ih := alt_update_smul_add T n
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [alt, Fin.tail_update_zero, Function.update_self, add_mul, smul_mul_assoc, ih,
        map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    · have h0 : ∀ w : R, Function.update x k.succ w 0 = x 0 := fun w =>
        Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
      have key : ∀ j : Fin n,
          alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k (a • u + v)) j
            (x 0 * Function.update (Fin.tail x) k (a • u + v) j)) =
          a * alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k u) j
            (x 0 * Function.update (Fin.tail x) k u j)) +
          alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k v) j
            (x 0 * Function.update (Fin.tail x) k v j)) := by
        intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self, Function.update_idem, mul_add, mul_smul_comm, ih]
        · simp only [Function.update_of_ne hj, Function.update_comm (Ne.symm hj), ih]
      simp only [alt, Fin.tail_update_succ, h0, key, ih, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

noncomputable def altMultilinear (T : R →ₗ[A] A) (n : ℕ) :
    MultilinearMap A (fun _ : Fin n => R) A :=
  MultilinearMap.mk' (alt (fun r => T r) n)
    (fun x i u v => by simpa using alt_update_smul_add T n x i 1 u v)
    (fun x i a u => by
      have h0 : alt (fun r => T r) n (Function.update x i 0) = 0 := by
        have := alt_update_smul_add T n x i 1 0 0
        simpa using this
      have := alt_update_smul_add T n x i a u 0
      simpa [h0] using this)

theorem altMultilinear_apply (T : R →ₗ[A] A) (n : ℕ) (x : Fin n → R) :
    altMultilinear T n x = alt (fun r => T r) n x := rfl

end Multilinear

theorem alt_comp_monoidHom {M N A : Type*} [Monoid M] [Monoid N] [CommRing A] (f : M →* N)
    (T : N → A) :
    ∀ (n : ℕ) (x : Fin n → M), alt T n (fun i => f (x i)) = alt (fun g => T (f g)) n x
  | 0, _ => rfl
  | n + 1, x => by
    have ih := alt_comp_monoidHom f T n
    have ht : Fin.tail (fun i => f (x i)) = fun i => f (Fin.tail x i) := rfl
    have hu : ∀ i : Fin n, Function.update (fun i => f (Fin.tail x i)) i (f (x 0) * f (Fin.tail x i)) =
        fun j => f (Function.update (Fin.tail x) i (x 0 * Fin.tail x i) j) := by
      intro i
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    simp only [alt, ht, hu, ih]

theorem exists_linear_extension (M A : Type) [Monoid M] [CommRing A] (d : ℕ) (T : M → A)
    (h : IsPsChar d T) :
    ∃ T' : MonoidAlgebra A M →ₗ[A] A, (∀ g, T' (MonoidAlgebra.of A M g) = T g) ∧
      IsPsChar d (fun x => T' x) := by
  let b : Module.Basis M A (MonoidAlgebra A M) := MonoidAlgebra.basis M A
  have hb : ∀ g, b g = MonoidAlgebra.of A M g := fun g => by simp [b]
  let T' : MonoidAlgebra A M →ₗ[A] A := b.constr A T
  have hT : ∀ g, T' (MonoidAlgebra.of A M g) = T g := fun g => by
    rw [← hb]; exact b.constr_basis A T g
  refine ⟨T', hT, ?_, ?_, ?_⟩
  · rw [← (MonoidAlgebra.of A M).map_one, hT, h.one]
  · intro x y
    have : (LinearMap.mul A (MonoidAlgebra A M)).compr₂ T' =
        (LinearMap.mul A (MonoidAlgebra A M)).flip.compr₂ T' := by
      refine b.ext fun g => b.ext fun k => ?_
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.mul_apply', hb,
        ← map_mul, hT]
      exact h.comm g k
    simpa using LinearMap.congr_fun₂ this x y
  · intro x
    have : altMultilinear T' (d + 1) = 0 := by
      refine Module.Basis.ext_multilinear (fun _ => b) fun g => ?_
      rw [altMultilinear_apply]
      simp only [hb, alt_comp_monoidHom, hT]
      exact h.alt_eq_zero g
    rw [← altMultilinear_apply, this]
    rfl

end GlobalTheory.PsChar
end

section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

open Polynomial

private theorem pseudo_character_sum_cons_expand {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ) (a : M)
    (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a r) =
      T a * _root_.GlobalTheory.PsChar.alt T n r -
        ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i)) := rfl

private theorem pseudo_character_sum_cons_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (ih : ∀ (w : Fin n → M) (τ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (w ∘ τ) = _root_.GlobalTheory.PsChar.alt T n w)
    (a : M) (w : Fin n → M) (τ : Equiv.Perm (Fin n)) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a (w ∘ τ)) =
      _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a w) := by
  rw [pseudo_character_sum_cons_expand, pseudo_character_sum_cons_expand, ih]
  congr 1
  have : ∀ i, Function.update (w ∘ τ) i (a * (w ∘ τ) i) =
      Function.update w (τ i) (a * w (τ i)) ∘ τ := fun i => by
    rw [Function.update_comp_equiv, Equiv.symm_apply_apply]; rfl
  simp only [this, ih]
  exact Equiv.sum_comp τ (fun j => _root_.GlobalTheory.PsChar.alt T n (Function.update w j (a * w j)))

private theorem alt_cons_cons_lemma_5 {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      T a * T b * _root_.GlobalTheory.PsChar.alt T n r
      - T a * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * r i))
      - T b * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i))
      - T (a * b) * _root_.GlobalTheory.PsChar.alt T n r
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * b * r i))
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i))
      + ∑ i, ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
  rw [pseudo_character_sum_cons_expand, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, Fin.cons_update, pseudo_character_sum_cons_expand]
  have hin : ∀ i : Fin n, ∑ l, _root_.GlobalTheory.PsChar.alt T n
      (Function.update (Function.update r i (a * r i)) l
        (b * Function.update r i (a * r i) l)) =
      _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) +
      ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
    intro i
    have hX : (∑ l : Fin n, if l = i then
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) else 0) =
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) := by simp
    rw [← hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [mul_assoc]
    · rw [if_neg hl, if_neg hl, zero_add, Function.update_of_ne hl]
  simp only [← Fin.cons_update, pseudo_character_sum_cons_expand, Finset.sum_sub_distrib, Function.update_self]
  simp only [hin, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem pseudo_character_sum_swap_head_pair {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) (n : ℕ) (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons b (Fin.cons a r)) := by
  rw [alt_cons_cons_lemma_5, alt_cons_cons_lemma_5, hc a b]
  have hoff : (∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l))) =
      ∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (b * r i)) l (a * r l)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · simp [hl]
    · rw [if_neg (Ne.symm hl), if_neg hl, Function.update_comm (Ne.symm hl)]
  rw [hoff]
  ring

private theorem pseudo_character_sum_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) :
    ∀ (n : ℕ) (v : Fin n → M) (σ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T n v := by
  intro n
  induction n with
  | zero => intro v σ; rfl
  | succ n ih =>
    have htail : ∀ (v : Fin (n + 1) → M) (i j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap i.succ j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v i j
      have hv : v ∘ Equiv.swap i.succ j.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j) := by
        funext k
        induction k using Fin.cases with
        | zero =>
          simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm]
        | succ k =>
          simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
          rw [(Fin.succ_injective n).swap_apply]
      rw [hv, pseudo_character_sum_cons_comp_perm T n ih, Fin.cons_self_tail]
    have h0 : ∀ (v : Fin (n + 1) → M) (j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap 0 j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v j
      cases n with
      | zero => exact j.elim0
      | succ m =>
        have h01 : ∀ v : Fin (m + 2) → M,
            _root_.GlobalTheory.PsChar.alt T (m + 2) (v ∘ Equiv.swap 0 (Fin.succ 0)) =
              _root_.GlobalTheory.PsChar.alt T (m + 2) v := by
          intro v
          obtain ⟨a, b, r, rfl⟩ : ∃ a b r, v = Fin.cons a (Fin.cons b r) :=
            ⟨_, _, _, (Fin.cons_self_tail v).symm.trans (congrArg _ (Fin.cons_self_tail _).symm)⟩
          have hv : (Fin.cons a (Fin.cons b r) : Fin (m + 2) → M) ∘ Equiv.swap 0 (Fin.succ 0) =
              Fin.cons b (Fin.cons a r) := by
            funext k
            refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
            · simp
            · simp
            · simp only [Function.comp_apply]
              rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
                (fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h))]
              simp
          rw [hv, pseudo_character_sum_swap_head_pair T hc]
        induction j using Fin.cases with
        | zero => exact h01 v
        | succ k =>
          have hp : Equiv.swap (0 : Fin (m + 2)) k.succ.succ =
              Equiv.swap (Fin.succ 0) k.succ.succ * Equiv.swap 0 (Fin.succ 0) *
                Equiv.swap (Fin.succ 0) k.succ.succ := by
            have h1 : Equiv.swap (Fin.succ 0) k.succ.succ (0 : Fin (m + 2)) = 0 :=
              Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero _).symm
            have h2 : Equiv.swap (Fin.succ 0) k.succ.succ (Fin.succ 0 : Fin (m + 2)) = k.succ.succ :=
              Equiv.swap_apply_left _ _
            have := Equiv.swap_apply_apply (Equiv.swap (Fin.succ 0) k.succ.succ) 0 (Fin.succ 0)
            rw [h1, h2, Equiv.swap_inv] at this
            exact this
          rw [hp, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
            ← Function.comp_assoc, htail, h01, htail]
    have hswap : ∀ (v : Fin (n + 1) → M) (x y : Fin (n + 1)),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap x y) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v x y
      induction x using Fin.cases with
      | zero =>
        induction y using Fin.cases with
        | zero => simp
        | succ j => exact h0 v j
      | succ i =>
        induction y using Fin.cases with
        | zero => rw [Equiv.swap_comm]; exact h0 v i
        | succ j => exact htail v i j
    intro v σ
    revert v
    refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ v : Fin (n + 1) → M,
      _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v)
      σ (fun v => rfl) ?_
    intro f x y _ hf v
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hswap]

open Polynomial in

theorem _root_.GlobalTheory.PsChar.cayleyHamilton (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : _root_.GlobalTheory.PsChar.IsPsChar d (fun x => T x)) (x : R) :
    ∃ p : Polynomial k, p.Monic ∧ p.natDegree = d ∧ ∀ y : R, T (Polynomial.aeval x p * y) = 0 := by
  have hc : ∀ a b : R, T (a * b) = T (b * a) := h.comm
  have hupd : ∀ (m : ℕ) (i : Fin (m + 1)) (w : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Function.update (fun _ => x) i w) =
        _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons w fun _ => x) := by
    intro m i w
    rw [← pseudo_character_sum_comp_perm _ hc (m + 1) _ (Equiv.swap 0 i)]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Function.comp_apply, Equiv.swap_apply_left, Function.update_self, Fin.cons_zero]
    · rw [Function.comp_apply, Fin.cons_succ, Function.update_of_ne]
      intro hj
      exact Fin.succ_ne_zero _
        ((Equiv.swap 0 i).injective (hj.trans (Equiv.swap_apply_left 0 i).symm))
  have hrec : ∀ (m : ℕ) (y : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 2) (Fin.cons y fun _ => x) =
        T y * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) -
          (m + 1) * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
            (Fin.cons (y * x) fun _ => x) := by
    intro m y
    rw [pseudo_character_sum_cons_expand]
    simp only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hcoef : ∀ m : ℕ, ∃ c : ℕ → k,
      (∀ y, _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons y fun _ => x) =
        ∑ j ∈ Finset.range (m + 1), c j * T (y * x ^ j)) ∧
      c m = (-1) ^ m * (m.factorial : k) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun y => ?_, by simp⟩
      rw [pseudo_character_sum_cons_expand]
      simp
      exact mul_one (T y)
    | succ m ih =>
      obtain ⟨c, hc1, hc2⟩ := ih
      refine ⟨fun j => if j = 0 then _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
        (fun _ => x) else -((m : k) + 1) * c (j - 1), fun y => ?_, ?_⟩
      · rw [hrec, hc1, Finset.sum_range_succ' _ (m + 1)]
        simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, pow_zero, mul_one,
          pow_succ', ← mul_assoc, Finset.mul_sum]
        rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · ring
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hc2, Nat.factorial_succ]
        push_cast
        ring
  obtain ⟨c, hc1, hc2⟩ := hcoef d
  have hzero : ∀ y, ∑ j ∈ Finset.range (d + 1), c j * T (y * x ^ j) = 0 := fun y =>
    (hc1 y).symm.trans (h.alt_eq_zero _)
  have hcd : c d ≠ 0 := by
    rw [hc2]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg : (∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt _
  refine ⟨X ^ d + ∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ), Polynomial.monic_X_pow_add hdeg, ?_,
    fun y => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  · have e := hzero y
    rw [Finset.sum_range_succ] at e
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
      add_mul, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i / c d * T (x ^ i * y)) d, hc]
    have hs : ∑ i ∈ Finset.range d, c i / c d * T (x ^ i * y) =
        (∑ i ∈ Finset.range d, c i * T (y * x ^ i)) / c d := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    rw [hs]
    field_simp
    linear_combination e

end GlobalTheory.PsChar
end

section
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

section
variable {M A : Type*} [Monoid M] [CommRing A]

theorem alt_const_idem (T : M → A) (e : M) (he : e * e = e) :
    ∀ n : ℕ, alt T n (fun _ => e) = ∏ i ∈ Finset.range n, (T e - (i : A))
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun _ : Fin (n + 1) => e) = fun _ : Fin n => e := rfl
    have h2 : ∀ i : Fin n, Function.update (fun _ : Fin n => e) i e = fun _ => e := by
      intro i; exact Function.update_eq_self i (fun _ : Fin n => e)
    rw [alt, h1]
    simp only [he, h2, alt_const_idem T e he n, Finset.prod_range_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem alt_idem_last (T : M → A) (e y : M) (he : e * e = e) (hy : e * y = y) (h0 : T e = 0) :
    ∀ n : ℕ, alt T (n + 1) (fun i => if i.val = n then y else e)
      = (-1) ^ n * (n.factorial : A) * T y
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun i : Fin (n + 1 + 1) => if i.val = n + 1 then y else e)
        = fun i : Fin (n + 1) => if i.val = n then y else e := by
      funext i; simp [Fin.tail]
    have h2 : ∀ i : Fin (n + 1), Function.update (fun i : Fin (n + 1) => if i.val = n then y else e) i
        (e * (if i.val = n then y else e)) = fun i => if i.val = n then y else e := by
      intro i
      have : e * (if i.val = n then y else e) = (if i.val = n then y else e) := by
        split_ifs <;> assumption
      rw [this]
      exact Function.update_eq_self i (fun i : Fin (n + 1) => if i.val = n then y else e)
    have h3 : (if ((0 : Fin (n + 1 + 1)) : ℕ) = n + 1 then y else e) = e := by simp
    rw [alt, h1, h3, h0]
    simp only [h2, alt_idem_last T e y he hy h0 n, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

end

theorem isPsChar_idempotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  intro k R _ _ _ _ d T hT e he
  have he' : e * e = e := he
  refine ⟨?_, fun h0 y => ?_⟩
  · have h := hT.alt_eq_zero (fun _ => e)
    rw [alt_const_idem _ e he', Finset.prod_eq_zero_iff] at h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), sub_eq_zero.mp h⟩
  · have h := hT.alt_eq_zero (fun i => if i.val = d then e * y else e)
    rw [alt_idem_last (fun x => T x) e (e * y) he' (by rw [← mul_assoc, he']) h0 d] at h
    have h1 : ((-1 : k) ^ d * (d.factorial : k)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
    exact (mul_eq_zero.mp h).resolve_left h1

end GlobalTheory.PsChar
end

open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  atlas_forward_decl GlobalTheory.PsChar.isPsChar_idempotent
end

section
section
namespace GlobalTheory.PsChar

theorem alt_pow_eq_prod {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (y : M)
    (hy : ∀ m, 2 ≤ m → T (y ^ m) = 0) :
    ∀ (n : ℕ) (z : Fin n → M), (∀ i, ∃ a, 1 ≤ a ∧ z i = y ^ a) → alt T n z = ∏ i, T (z i)
  | 0, _, _ => by simp [alt]
  | n + 1, z, hz => by
    rw [alt, alt_pow_eq_prod T y hy n (Fin.tail z) (fun i => hz i.succ), Fin.prod_univ_succ]
    have hs : ∑ i : Fin n, alt T n (Function.update (Fin.tail z) i (z 0 * Fin.tail z i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      obtain ⟨a, ha, hza⟩ := hz 0
      obtain ⟨b, hb, hzb⟩ := hz i.succ
      have he : z 0 * Fin.tail z i = y ^ (a + b) := by
        rw [pow_add, ← hza, ← hzb]; rfl
      rw [he, alt_pow_eq_prod T y hy n]
      · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [Function.update_self]
        exact hy _ (by omega)
      · intro j
        by_cases hj : j = i
        · subst hj
          exact ⟨a + b, by omega, by rw [Function.update_self]⟩
        · rw [Function.update_of_ne hj]
          exact hz j.succ
    rw [hs, sub_zero]
    rfl

theorem IsPsChar.apply_eq_zero_of_pow {M A : Type*} [Monoid M] [CommRing A] [IsReduced A] {d : ℕ} {T : M → A}
    (hT : IsPsChar d T) (y : M) (hy : ∀ m, 2 ≤ m → T (y ^ m) = 0) : T y = 0 := by
  have h := alt_pow_eq_prod T y hy (d + 1) (fun _ => y) (fun _ => ⟨1, le_rfl, (pow_one y).symm⟩)
  rw [hT.alt_eq_zero] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact IsNilpotent.eq_zero ⟨d + 1, h.symm⟩

theorem apply_eq_zero_of_isNilpotent (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ)
    (T : R →ₗ[k] k) (hT : IsPsChar d (fun x => T x)) (x : R) (hx : IsNilpotent x) : T x = 0 := by
  obtain ⟨N, hN⟩ := hx
  have key : ∀ r j : ℕ, 1 ≤ j → N ≤ j + r → T (x ^ j) = 0 := by
    intro r
    induction r with
    | zero =>
      intro j _ hj
      rw [pow_eq_zero_of_le (by simpa using hj) hN, map_zero]
    | succ r ih =>
      intro j h1 hj
      refine hT.apply_eq_zero_of_pow (x ^ j) fun m hm => ?_
      show T ((x ^ j) ^ m) = 0
      rw [← pow_mul]
      have : j * 2 ≤ j * m := Nat.mul_le_mul_left j hm
      exact ih _ (by omega) (by omega)
  simpa using key N 1 le_rfl (by omega)

end GlobalTheory.PsChar
end

open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ x : R, IsNilpotent x → T x = 0 := by
  atlas_forward_decl GlobalTheory.PsChar.apply_eq_zero_of_isNilpotent
end

section
namespace GlobalTheory.AlgRing

private theorem exists_idempotent_of_not_isNilpotent (k R : Type) [Field k] [Ring R] [Algebra k R]
    (x : R) (hx : IsIntegral k x) (hn : ¬ IsNilpotent x) :
    ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ ∃ q : Polynomial k, e = x * Polynomial.aeval x q := by
  have hp0 : minpoly k x ≠ 0 := minpoly.ne_zero hx
  obtain ⟨g, hpg, hg⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k x) hp0 0
  simp only [map_zero, sub_zero] at hpg hg
  set s := Polynomial.rootMultiplicity 0 (minpoly k x)
  have hcop : IsCoprime (Polynomial.X ^ (s + 1)) g :=
    (Polynomial.irreducible_X.coprime_iff_not_dvd.mpr hg).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have hev : Polynomial.aeval x (Polynomial.X ^ s * g) = 0 := by
    rw [← hpg]; exact minpoly.aeval k x
  have hE : ∀ P : Polynomial k,
      Polynomial.aeval x (P * (Polynomial.X ^ s * g)) = 0 := fun P => by rw [map_mul, hev, mul_zero]
  refine ⟨Polynomial.aeval x (a * Polynomial.X ^ (s + 1)), ?_, ?_, ⟨a * Polynomial.X ^ s, ?_⟩⟩
  · have hpoly : (a * Polynomial.X ^ (s + 1)) * (a * Polynomial.X ^ (s + 1)) =
        a * Polynomial.X ^ (s + 1) + (-(a * b * Polynomial.X)) * (Polynomial.X ^ s * g) := by
      linear_combination (a * Polynomial.X ^ (s + 1)) * hab
    unfold IsIdempotentElem
    rw [← map_mul, hpoly, map_add, hE, add_zero]
  · intro he
    apply hn
    refine ⟨s, ?_⟩
    have hpoly : (Polynomial.X : Polynomial k) ^ s =
        Polynomial.X ^ s * (a * Polynomial.X ^ (s + 1)) + b * (Polynomial.X ^ s * g) := by
      linear_combination (Polynomial.X ^ s) * hab.symm
    have := congrArg (Polynomial.aeval x) hpoly
    rwa [map_add, hE, add_zero, map_mul, he, mul_zero, map_pow, Polynomial.aeval_X] at this
  · have h : a * Polynomial.X ^ (s + 1) = Polynomial.X * (a * Polynomial.X ^ s) := by ring
    rw [h, map_mul, Polynomial.aeval_X]

private theorem exists_idempotent_mem_left_multiples (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0)
    (x : R) (hx : x ≠ 0) : ∃ e r : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e = r * x := by
  have : ¬ ∀ y : R, IsNilpotent (y * x) := fun h => hx (hnil x h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  obtain ⟨e, he, he0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R (y * x) (hint _) hy
  have hcomm : Commute (y * x) (Polynomial.aeval (y * x) q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval (y * x))
  refine ⟨_, Polynomial.aeval (y * x) q * y, he, he0, ?_⟩
  rw [hcomm.eq, mul_assoc]

private theorem sum_eq_one_of_maximal_orthogonalIdempotents (k R : Type) [Field k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False) :
    ∑ i, e i = 1 := by
  by_contra hsum
  set f := 1 - ∑ i, e i with hfdef
  have hf0 : f ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
  have hS : IsIdempotentElem (∑ i, e i) := he.isIdempotentElem_sum
  have hf : IsIdempotentElem f := hS.one_sub
  have hef : ∀ i, e i * f = 0 := fun i => by
    rw [hfdef, mul_sub, mul_one, he.mul_sum_of_mem (Finset.mem_univ i), sub_self]
  have hfe : ∀ i, f * e i = 0 := fun i => by
    rw [hfdef, sub_mul, one_mul, Finset.sum_mul,
      Finset.sum_eq_single i (fun j _ hj => he.ortho hj) (by simp), (he.idem i).eq, sub_self]
  obtain ⟨e', r, he', he'0, rfl⟩ :=
    exists_idempotent_mem_left_multiples k R hint hnil f hf0
  have hg : IsIdempotentElem (f * (r * f)) := by
    unfold IsIdempotentElem
    calc f * (r * f) * (f * (r * f)) = f * (r * (f * f)) * (r * f) := by noncomm_ring
      _ = f * (r * f) := by rw [hf.eq, mul_assoc, he'.eq]
  have hg0 : f * (r * f) ≠ 0 := by
    intro h0
    apply he'0
    rw [← he'.eq, mul_assoc, h0, mul_zero]
  refine hmax (Fin.cons (f * (r * f)) e) ⟨fun i => ?_, fun i j hij => ?_⟩ fun i => ?_
  · refine Fin.cases hg (fun i => ?_) i
    simpa using he.idem i
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simp only [Fin.cons_zero, Fin.cons_succ]; rw [mul_assoc, mul_assoc, hfe, mul_zero, mul_zero]
    | succ i =>
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ]; rw [← mul_assoc, hef, zero_mul]
      | succ j =>
        simp only [Fin.cons_succ]
        exact he.ortho fun h => hij (by rw [h])
  · refine Fin.cases hg0 (fun i => ?_) i
    simpa using hne i

private theorem not_isNilpotent_mul_mul_of_mul_eq_of_not_isNilpotent {R : Type} [Ring R] (f a y : R) (hl : f * a = a)
    (hy : ¬ IsNilpotent (y * a)) : ¬ IsNilpotent (a * y * f) := by
  have hpow : ∀ j : ℕ, (a * y) ^ (j + 1) = (a * y * f) ^ j * (a * y) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (a * y) (j + 1), ih, pow_succ (a * y * f) j, mul_assoc ((a * y * f) ^ j),
        mul_assoc ((a * y * f) ^ j)]
      congr 1
      rw [mul_assoc (a * y) f, ← mul_assoc f a y, hl]
  rintro ⟨n, hn⟩
  have hya : ∀ j : ℕ, (y * a) ^ (j + 1) = y * (a * y) ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, pow_succ]; simp only [mul_assoc]
  exact hy ⟨n + 2, by rw [hya, hpow, hn, zero_mul, mul_zero, zero_mul]⟩

private theorem eq_of_idempotent_in_corner_of_maximal {R : Type} [Ring R] {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (f : R) (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hl : e i * f = f)
    (hr : f * e i = f) : f = e i := by
  by_contra hfe
  have hg : IsIdempotentElem (e i - f) := by
    unfold IsIdempotentElem
    rw [sub_mul, mul_sub, mul_sub, (he.idem i).eq, hl, hr, hf.eq]; abel
  have hg0 : e i - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfe)
  have hgf : (e i - f) * f = 0 := by rw [sub_mul, hl, hf.eq, sub_self]
  have hfg : f * (e i - f) = 0 := by rw [mul_sub, hr, hf.eq, sub_self]
  have hjf : ∀ j, j ≠ i → e j * f = 0 := fun j hj => by rw [← hl, ← mul_assoc, he.ortho hj, zero_mul]
  have hfj : ∀ j, j ≠ i → f * e j = 0 := fun j hj => by rw [← hr, mul_assoc, he.ortho hj.symm, mul_zero]
  have hjg : ∀ j, j ≠ i → e j * (e i - f) = 0 := fun j hj => by rw [mul_sub, he.ortho hj, hjf j hj, sub_self]
  have hgj : ∀ j, j ≠ i → (e i - f) * e j = 0 := fun j hj => by rw [sub_mul, he.ortho hj.symm, hfj j hj, sub_self]
  set u := Function.update e i f
  have hu : ∀ j, u j = if j = i then f else e j := fun j => Function.update_apply e i f j
  refine hmax (Fin.cons (e i - f) u) ⟨fun j => ?_, fun a b hab => ?_⟩ fun j => ?_
  · refine Fin.cases hg (fun j => ?_) j
    simp only [Fin.cons_succ, hu]; split_ifs
    · exact hf
    · exact he.idem j
  · induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b =>
        simp only [Fin.cons_zero, Fin.cons_succ, hu]; split_ifs with hb
        · exact hgf
        · exact hgj b hb
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ, hu]; split_ifs with ha
        · exact hfg
        · exact hjg a ha
      | succ b =>
        have hab' : a ≠ b := fun h => hab (by rw [h])
        simp only [Fin.cons_succ, hu]
        split_ifs with ha hb hb
        · exact absurd (ha.trans hb.symm) hab'
        · exact hfj b hb
        · exact hjf a ha
        · exact he.ortho hab'
  · refine Fin.cases hg0 (fun j => ?_) j
    simp only [Fin.cons_succ, hu]; split_ifs
    · exact hf0
    · exact hne j

private theorem exists_right_inverse_in_corner_of_not_isNilpotent (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) (hz : ¬ IsNilpotent z) :
    ∃ t, e i * t = t ∧ z * t = e i := by
  obtain ⟨f, hf, hf0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R z (hint z) hz
  have hcomm : Commute z (Polynomial.aeval z q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval z)
  have hfl : e i * (z * Polynomial.aeval z q) = z * Polynomial.aeval z q := by
    rw [← mul_assoc, hl]
  have hfr : z * Polynomial.aeval z q * e i = z * Polynomial.aeval z q := by
    rw [hcomm.eq, mul_assoc, hr]
  have hfe := eq_of_idempotent_in_corner_of_maximal e he hne hmax i _ hf hf0 hfl hfr
  refine ⟨e i * Polynomial.aeval z q, by rw [← mul_assoc, (he.idem i).eq], ?_⟩
  rw [← mul_assoc, hr, hfe]

private theorem eq_zero_of_isNilpotent_in_corner_of_maximal (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0)
    {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (w : R) (hl : e i * w = w) (hr : w * e i = w) (hw : IsNilpotent w) : w = 0 := by
  by_contra hw0
  have : ¬ ∀ y : R, IsNilpotent (y * w) := fun h => hw0 (hnil w h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  have hpow : ∀ j : ℕ, (w * y) ^ (j + 1) = (w * y * e i) ^ j * (w * y) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (w * y) (j + 1), ih, pow_succ (w * y * e i) j, mul_assoc ((w * y * e i) ^ j),
        mul_assoc ((w * y * e i) ^ j)]
      congr 1
      rw [mul_assoc (w * y) (e i), ← mul_assoc (e i) w y, hl]
  have hu : ¬ IsNilpotent (w * y * e i) := by
    rintro ⟨n, hn⟩
    have hyw : ∀ j : ℕ, (y * w) ^ (j + 1) = y * (w * y) ^ j * w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, pow_succ]; simp only [mul_assoc]
    exact hy ⟨n + 2, by rw [hyw, hpow, hn, zero_mul, mul_zero, zero_mul]⟩
  obtain ⟨t, het, hut⟩ := exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i (w * y * e i)
    (by rw [← mul_assoc, ← mul_assoc, hl]) (by rw [mul_assoc, (he.idem i).eq]) hu
  set s := e i * (y * e i * t)
  have hs : e i * s = s := by rw [← mul_assoc, (he.idem i).eq]
  have hws : w * s = e i := by
    have h3 : w * (y * e i * t) = w * y * e i * t := by simp only [mul_assoc]
    rw [← mul_assoc, hr, h3, hut]
  have hj : ∀ j : ℕ, e i = w ^ (j + 1) * s ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp [hws]
    | succ j ih =>
      rw [pow_succ w (j + 1), pow_succ' s (j + 1), mul_assoc, ← mul_assoc w s, hws,
        pow_succ' s j, ← mul_assoc (e i) s, hs, ← pow_succ']
      exact ih
  obtain ⟨N, hN⟩ := hw
  apply hne i
  rw [hj N, pow_succ, hN, zero_mul, zero_mul]

private theorem exists_eq_smul_idempotent_of_mem_corner (k R : Type) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) : ∃ c : k, z = c • e i := by
  by_cases hz : IsNilpotent z
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    exact eq_zero_of_isNilpotent_in_corner_of_maximal k R hint hnil e he hne hmax i z hl hr hz
  have hp0 : minpoly k z ≠ 0 := minpoly.ne_zero (hint z)
  obtain ⟨g, hpg, hg⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k z) hp0 0
  simp only [map_zero, sub_zero] at hpg hg
  set s := Polynomial.rootMultiplicity 0 (minpoly k z)
  have hev : Polynomial.aeval z (Polynomial.X ^ s * g) = 0 := by
    rw [← hpg]; exact minpoly.aeval k z
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hpg; exact hp0 hpg
  have hgdeg : g.degree ≠ 0 := by
    intro h0
    rw [Polynomial.eq_C_of_degree_eq_zero h0, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at hev
    have hc : g.coeff 0 ≠ 0 := fun h => hg (Polynomial.X_dvd_iff.mpr h)
    exact hz ⟨s, by simpa [hc] using hev⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root g hgdeg
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hg (by simpa using Polynomial.dvd_iff_isRoot.mpr hc)
  by_contra hno
  push_neg at hno
  set w := z - c • e i with hw
  have hei : e i * e i = e i := (he.idem i).eq
  have hwl : e i * w = w := by rw [hw, mul_sub, hl, mul_smul_comm, hei]
  have hwr : w * e i = w := by rw [hw, sub_mul, hr, smul_mul_assoc, hei]
  have hwn : ¬ IsNilpotent w := fun hn => hno c (sub_eq_zero.mp
    (eq_zero_of_isNilpotent_in_corner_of_maximal k R hint hnil e he hne hmax i w hwl hwr hn))
  obtain ⟨t, het, hwt⟩ := exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i w hwl hwr hwn
  have hzu : Polynomial.aeval z (Polynomial.X - Polynomial.C c) *
      (t - c⁻¹ • (1 - e i)) = 1 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    have h1 : z * t - c • t = e i := by
      rw [← hwt, hw, sub_mul, smul_mul_assoc, het]
    have h2 : (z - c • (1 : R)) * (1 - e i) = -(c • (1 - e i)) := by
      simp only [mul_sub, sub_mul, mul_one, one_mul, hr, smul_mul_assoc, smul_sub]
      abel
    rw [mul_sub, mul_smul_comm, h2, smul_neg, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      sub_mul, smul_mul_assoc, one_mul, h1]
    abel
  obtain ⟨h, hh⟩ : ∃ h, g = (Polynomial.X - Polynomial.C c) * h :=
    Polynomial.dvd_iff_isRoot.mpr hc
  have hcomm : Polynomial.X ^ s * g = (Polynomial.X ^ s * h) * (Polynomial.X - Polynomial.C c) := by
    rw [hh]; ring
  have hzero : Polynomial.aeval z (Polynomial.X ^ s * h) = 0 := by
    rw [hcomm, map_mul] at hev
    have := congrArg (· * (t - c⁻¹ • (1 - e i))) hev
    rwa [mul_assoc, hzu, mul_one, zero_mul] at this
  have hh0 : Polynomial.X ^ s * h ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) ?_
    rintro rfl; exact hg0 (by rw [hh, mul_zero])
  have hdeg := minpoly.degree_le_of_ne_zero k z hh0 hzero
  rw [hpg, hcomm, Polynomial.degree_mul, Polynomial.degree_X_sub_C] at hdeg
  have hfin : (Polynomial.X ^ s * h).degree ≠ ⊥ := by
    rwa [Ne, Polynomial.degree_eq_bot]
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hfin
  rw [← hn] at hdeg
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at hdeg
  omega

private theorem exists_smul_eq_corner_of_maximal_orthogonalIdempotents (k R : Type) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i j : Fin m) : ∃ a : R, ∀ r : R, ∃ c : k, e i * r * e j = c • a := by
  by_cases h : ∀ r, e i * r * e j = 0
  · exact ⟨0, fun r => ⟨0, by rw [h r, smul_zero]⟩⟩
  push_neg at h
  obtain ⟨r0, ha0⟩ := h
  set a := e i * r0 * e j
  have hii : e i * e i = e i := (he.idem i).eq
  have hjj : e j * e j = e j := (he.idem j).eq
  have hal : e i * a = a := by simp only [a, ← mul_assoc, hii]
  have har : a * e j = a := by simp only [a, mul_assoc, hjj]
  have : ¬ ∀ y : R, IsNilpotent (y * a) := fun h => ha0 (hnil a h)
  push_neg at this
  obtain ⟨y, hy⟩ := this
  have hu := not_isNilpotent_mul_mul_of_mul_eq_of_not_isNilpotent (e i) a y hal hy
  obtain ⟨ν, hν⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i (a * y * e i)
    (by rw [← mul_assoc, ← mul_assoc, hal]) (by rw [mul_assoc, hii])
  have hν0 : ν ≠ 0 := by
    rintro rfl; rw [zero_smul] at hν; exact hu (by rw [hν]; exact IsNilpotent.zero)
  set b := ν⁻¹ • (e j * y * e i)
  have hab : a * b = e i := by
    simp only [b, mul_smul_comm, ← mul_assoc, har]
    rw [hν, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hbe : b * e i = b := by simp only [b, smul_mul_assoc, mul_assoc, hii]
  obtain ⟨μ, hμ⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax j (b * a)
    (by simp only [b, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hjj]) (by rw [mul_assoc, har])
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    apply ha0
    rw [← hal, ← hab, mul_assoc, hμ, mul_zero]
  refine ⟨a, fun r => ?_⟩
  set c := e i * r * e j
  have hcl : e i * c = c := by simp only [c, ← mul_assoc, hii]
  have hcr : c * e j = c := by simp only [c, mul_assoc, hjj]
  obtain ⟨l, hl⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i (c * b)
    (by rw [← mul_assoc, hcl]) (by rw [mul_assoc, hbe])
  refine ⟨μ⁻¹ * l, ?_⟩
  calc c = c * e j := hcr.symm
    _ = μ⁻¹ • (c * (b * a)) := by rw [hμ, mul_smul_comm, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    _ = (μ⁻¹ * l) • a := by rw [← mul_assoc, hl, smul_mul_assoc, hal, smul_smul]

theorem _root_.GlobalTheory.AlgRing.finite_and_isSemisimpleRing :
    ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ),
      (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) →
      (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) →
      Module.Finite k R ∧ IsSemisimpleRing R := by
  intro k R _ _ _ _ d hint hnil hidem
  have hfin : Module.Finite k R := by
    classical
    let P : ℕ → Prop := fun m => ∃ e : Fin m → R, OrthogonalIdempotents e ∧ ∀ i, e i ≠ 0
    have hP0 : P 0 := ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
    obtain ⟨e, he, hne⟩ : P (Nat.findGreatest P d) := Nat.findGreatest_spec (Nat.zero_le d) hP0
    have hmax : ∀ e' : Fin (Nat.findGreatest P d + 1) → R, OrthogonalIdempotents e' →
        (∀ i, e' i ≠ 0) → False := fun e' he' hne' =>
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hidem _ e' he' hne') ⟨e', he', hne'⟩
    have hsum := sum_eq_one_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax
    choose a ha using fun p : Fin (Nat.findGreatest P d) × Fin (Nat.findGreatest P d) =>
      exists_smul_eq_corner_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax p.1 p.2
    refine ⟨⟨Finset.univ.image a, eq_top_iff.mpr fun r _ => ?_⟩⟩
    have hr : r = (∑ i, e i) * r * (∑ j, e j) := by rw [hsum, one_mul, mul_one]
    rw [hr]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := ha (i, j) r
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  refine ⟨hfin, ?_⟩
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  refine IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (eq_bot_iff.mpr fun x hx => ?_)
  rw [Submodule.mem_bot]
  refine hnil x fun y => ?_
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hx' : x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ring.jacobson_eq_sInf_isMaximal] at hx
    exact Submodule.mem_sInf.mpr fun J hJ => Submodule.mem_sInf.mp hx J hJ.2
  have hyx : y * x ∈ Ideal.jacobson (⊥ : Ideal R) := Ideal.mul_mem_left _ y hx'
  have := Ideal.pow_mem_pow hyx n
  rw [hn] at this
  exact ⟨n, by simpa using this⟩

end GlobalTheory.AlgRing
end

section
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  atlas_forward_decl GlobalTheory.AlgRing.finite_and_isSemisimpleRing
end

section
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add, Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
end

open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range : ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k), IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  atlas_forward_decl GlobalTheory.isSSRep_of_isSemisimpleRing_range
end

section
section
namespace GlobalTheory

open Matrix

theorem linearForm_matrix_eq_smul_trace_of_comm (k : Type) [Field k] (m : ℕ)
    (t : Matrix (Fin m) (Fin m) k →ₗ[k] k) (ht : ∀ x y, t (x * y) = t (y * x)) :
    ∃ c : k, ∀ x, t x = c * x.trace := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : k, t (single (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ 1) = c := ⟨_, rfl⟩
    refine ⟨c, fun x => ?_⟩
    set o : Fin m := ⟨0, hm⟩
    have key : ∀ a b : Fin m, t (single a b 1) = if a = b then c else 0 := by
      intro a b
      split_ifs with hab
      · subst hab
        have h1 : single a a (1 : k) = single a o 1 * single o a 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single o o (1 : k) = single o a 1 * single a o 1 := by
          rw [single_mul_single_same, mul_one]
        rw [h1, ht, ← h2, hc]
      · have h1 : single a b (1 : k) = single a a 1 * single a b 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single a b (1 : k) * single a a 1 = 0 :=
          single_mul_single_of_ne (1 : k) a b a (Ne.symm hab) 1
        rw [h1, ht, h2, map_zero]
    have hx : x = ∑ a, ∑ b, x a b • single a b (1 : k) := by
      conv_lhs => rw [matrix_eq_sum_single x]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]

theorem centralLinearForm_pi_matrix_eq_sum_trace :
    ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ)
      (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k),
      (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  intro k _ N n τ hτ
  have h : ∀ i, ∃ c : k, ∀ A, (τ ∘ₗ LinearMap.single k (fun i => Matrix (Fin (n i)) (Fin (n i)) k) i) A
      = c * A.trace := by
    intro i
    refine linearForm_matrix_eq_smul_trace_of_comm k (n i) _ fun A B => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Pi.single_mul, Pi.single_mul, hτ]
  choose c hc using h
  refine ⟨c, fun x => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hc i (x i)
  simpa using this

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix : ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ) (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k), (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  atlas_forward_decl GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace
end

section
section
namespace GlobalTheory

open Matrix

noncomputable def blockDiagMultAlgHom (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k]
      Matrix (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) k where
  toFun x := blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)
  map_one' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 1
    exact blockDiagonal'_one
  map_mul' x y := by
    simp only [Pi.mul_apply]
    exact blockDiagonal'_mul _ _
  map_zero' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (0 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 0
    exact blockDiagonal'_zero
  map_add' x y := by
    simp only [Pi.add_apply]
    exact (blockDiagonal'_add _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply]
    rw [show (fun j : (Σ i, Fin (m i)) => r • (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k))
        = r • (fun j => 1) from rfl, blockDiagonal'_smul]
    congr 1
    exact blockDiagonal'_one

theorem blockDiagMultAlgHom_trace (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ)
    (x : Π i, Matrix (Fin (n i)) (Fin (n i)) k) :
    (blockDiagMultAlgHom k N n m x).trace = ∑ i, (m i : k) * (x i).trace := by
  show (blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)).trace = _
  rw [trace_blockDiagonal', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _y : Fin (m i), (x i).trace = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_algHom_trace_eq_sum_mult_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ),
    ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k,
      ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  intro k _ N n m d hd
  have hcard : Fintype.card (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) = d := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, ← hd]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(reindexAlgEquiv k k e).toAlgHom.comp (blockDiagMultAlgHom k N n m), fun x => ?_⟩
  rw [← blockDiagMultAlgHom_trace]
  show (reindex e e (blockDiagMultAlgHom k N n m x)).trace = _
  simp only [reindex_apply, trace, diag, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => blockDiagMultAlgHom k N n m x i i)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ), ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k, ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  atlas_forward_decl GlobalTheory.exists_algHom_trace_eq_sum_mult_trace
end

section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
end
