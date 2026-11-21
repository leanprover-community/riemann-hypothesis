import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

section
open Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma antitone_prod_pow_dominance (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) :
    ∀ N : ℕ, (∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a) →
      ∀ c : ℝ, 0 ≤ c → (∀ a < N, c ≤ t a) →
      (∏ a ∈ range N, t a ^ μ a) * c ^ (∑ a ∈ range N, lam a - ∑ a ∈ range N, μ a) ≤
        ∏ a ∈ range N, t a ^ lam a := by
  intro N
  induction N with
  | zero => intro _ c _ _; simp
  | succ N ih =>
    intro hS c hc hct
    have hSN : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a := fun k hk => hS k (by omega)
    have hN := hS N (by omega)
    have hN1 := hS (N + 1) le_rfl
    simp only [Finset.sum_range_succ, Finset.prod_range_succ] at hN1 ⊢
    set Pm := ∏ a ∈ range N, t a ^ μ a with hPm
    set Pl := ∏ a ∈ range N, t a ^ lam a with hPl
    set M := ∑ a ∈ range N, μ a with hM
    set L := ∑ a ∈ range N, lam a with hL
    have htN : 0 ≤ t N := ht0 N
    have hPm0 : 0 ≤ Pm := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hPl0 : 0 ≤ Pl := Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
    have hcN : c ≤ t N := hct N (by omega)
    rcases le_total (μ N) (lam N) with h | h
    · have e : L + lam N - (M + μ N) = (L - M) + (lam N - μ N) := by omega
      rw [e, pow_add]
      have ih' := ih hSN c hc (fun a ha => hct a (by omega))
      have h2 : t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ lam N := by
        calc t N ^ μ N * c ^ (lam N - μ N) ≤ t N ^ μ N * t N ^ (lam N - μ N) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _) (pow_nonneg htN _)
          _ = t N ^ lam N := by rw [← pow_add, Nat.add_sub_cancel' h]
      calc Pm * t N ^ μ N * (c ^ (L - M) * c ^ (lam N - μ N))
          = (Pm * c ^ (L - M)) * (t N ^ μ N * c ^ (lam N - μ N)) := by ring
        _ ≤ Pl * t N ^ lam N :=
          mul_le_mul ih' h2 (mul_nonneg (pow_nonneg htN _) (pow_nonneg hc _)) hPl0
    · have ih' := ih hSN (t N) htN (fun a ha => ht (show a ≤ N by omega))
      have e2 : t N ^ μ N * t N ^ (L + lam N - (M + μ N)) = t N ^ (L - M) * t N ^ lam N := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc Pm * t N ^ μ N * c ^ (L + lam N - (M + μ N))
          ≤ Pm * t N ^ μ N * t N ^ (L + lam N - (M + μ N)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hcN _)
              (mul_nonneg hPm0 (pow_nonneg htN _))
        _ = Pm * t N ^ (L - M) * t N ^ lam N := by rw [mul_assoc, e2, ← mul_assoc]
        _ ≤ Pl * t N ^ lam N := mul_le_mul_of_nonneg_right ih' (pow_nonneg htN _)

lemma ldiag_domPow_nat (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) (N : ℕ)
    (hS : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a)
    (hT : ∑ a ∈ range N, μ a = ∑ a ∈ range N, lam a) :
    ∏ a ∈ range N, t a ^ μ a ≤ ∏ a ∈ range N, t a ^ lam a := by
  have h := antitone_prod_pow_dominance t ht0 ht μ lam N hS 0 le_rfl (fun a _ => ht0 a)
  rwa [hT, Nat.sub_self, pow_zero, mul_one] at h

def ldiagExt {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : ℕ) : α :=
  if h : a < r then f ⟨a, h⟩ else 0

lemma ldiag_ext_fin {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : Fin r) : ldiagExt f a = f a := by
  rw [ldiagExt, dif_pos a.isLt]

lemma ldiag_sum_filter_lt_eq_range {r : ℕ} (f : Fin r → ℕ) (k : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r with a.val < k, f a = ∑ a ∈ range k, ldiagExt f a := by
  rw [Finset.sum_filter]
  have h1 : ∀ a : Fin r, (if a.val < k then f a else 0) =
      (fun i : ℕ => if i < k then ldiagExt f i else 0) a.val := fun a => by
    simp only [ldiag_ext_fin]
  rw [Finset.sum_congr rfl (fun a _ => h1 a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then ldiagExt f i else 0) r, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

lemma ldiag_sum_univ_eq_range {r : ℕ} (f : Fin r → ℕ) :
    ∑ a : Fin r, f a = ∑ a ∈ range r, ldiagExt f a := by
  have h := ldiag_sum_filter_lt_eq_range f r le_rfl
  simpa using h

lemma ldiag_prod_univ_eq_range {r : ℕ} (t : Fin r → ℝ) (μ : Fin r → ℕ) :
    ∏ a : Fin r, t a ^ μ a = ∏ a ∈ range r, ldiagExt t a ^ ldiagExt μ a := by
  rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => ldiagExt t i ^ ldiagExt μ i) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [ldiag_ext_fin]

theorem dominancePowerProduct_holds : DomPow := by
  intro r t μ lam ht0 ht hS hT
  rw [ldiag_prod_univ_eq_range, ldiag_prod_univ_eq_range]
  have hext0 : ∀ a, 0 ≤ ldiagExt t a := fun a => by
    unfold ldiagExt; split_ifs
    · exact ht0 _
    · exact le_rfl
  refine ldiag_domPow_nat (ldiagExt t) hext0 ?_ (ldiagExt μ) (ldiagExt lam) r ?_ ?_
  · intro a b hab
    by_cases hb : b < r
    · have ha : a < r := lt_of_le_of_lt hab hb
      simp only [ldiagExt, dif_pos ha, dif_pos hb]
      exact ht (show (⟨a, ha⟩ : Fin r) ≤ ⟨b, hb⟩ from hab)
    · simp only [ldiagExt, dif_neg hb]
      exact hext0 a
  · intro k hk
    rw [← ldiag_sum_filter_lt_eq_range μ k hk, ← ldiag_sum_filter_lt_eq_range lam k hk]
    exact hS k
  · rw [← ldiag_sum_univ_eq_range, ← ldiag_sum_univ_eq_range]
    exact hT

end Formalism.GradedWeylDivisibility
end
end

section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

open Formalism.REAL (fockF)

lemma ldiag_rowAct_diag_eq {r n : ℕ} (t : Fin r → ℂ) :
    rowAct ℂ (n := n) (Matrix.diagonal t) = aeval fun v : Fin r × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma ldiag_prod_rowDeg {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) :
    (u.prod fun v k => t v.1 ^ k) = ∏ a : Fin r, t a ^ rowDeg u a := by
  have h1 : (u.prod fun v k => t v.1 ^ k) = ∏ v : Fin r × Fin n, t v.1 ^ u v := by
    exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  rw [h1]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  try dsimp only
  rw [Finset.prod_pow_eq_pow_sum, rowDeg]

lemma ldiag_aeval_monomial {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    aeval (fun v : Fin r × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin r, t a ^ rowDeg u a) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, ← ldiag_prod_rowDeg,
    MvPolynomial.algebraMap_eq, MvPolynomial.C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

lemma ldiag_coeff_rowAct_diag {r n : ℕ} (t : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal t) f) = coeff m f * ∏ a : Fin r, t a ^ rowDeg m a := by
  rw [ldiag_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on'
  next u c =>
    rw [ldiag_aeval_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · rw [zero_mul]
  next p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma ldiag_term (z : ℂ) (w : ℝ) (N : ℕ) :
    z * (w : ℂ) * star (z * (w : ℂ)) * (N : ℂ) = ((Complex.normSq z * w ^ 2 * N : ℝ) : ℂ) := by
  have hs : ∀ x : ℂ, star x = (starRingEnd ℂ) x := fun _ => rfl
  apply Complex.ext
  all_goals
    simp only [hs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring

lemma ldiag_term0 (z : ℂ) (N : ℕ) :
    z * star z * (N : ℂ) = ((Complex.normSq z * N : ℝ) : ℂ) := by
  have hs : ∀ x : ℂ, star x = (starRingEnd ℂ) x := fun _ => rfl
  apply Complex.ext
  all_goals
    simp only [hs, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring

private theorem mul_sq_mul_le_sq_mul_mul_of_le {c N p q : ℝ} (hc : 0 ≤ c) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hpq : p ≤ q) : c * p ^ 2 * N ≤ q ^ 2 * (c * N) := by
  have h1 : p * p ≤ q * q := mul_self_le_mul_self hp hpq
  have h2 : 0 ≤ c * N := mul_nonneg hc hN
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  calc c * p ^ 2 * N = (p * p) * (c * N) := by ring
    _ ≤ (q * q) * (c * N) := h3
    _ = q ^ 2 * (c * N) := by ring

theorem fockDiagBound_of (h : DomPow) : FockDiagBound := by
  unfold DomPow at h
  unfold FockDiagBound
  intro r n t lam ht0 ht f hdom hsum
  have hcoeff : ∀ m, coeff m (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f) =
      coeff m f * ((∏ a : Fin r, t a ^ rowDeg m a : ℝ) : ℂ) := by
    intro m
    simp only [ldiag_coeff_rowAct_diag, Complex.ofReal_prod, Complex.ofReal_pow]
  have hsupp : (rowAct ℂ (Matrix.diagonal fun a => (t a : ℂ)) f).support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hcoeff, h0, zero_mul])
  have hq : ∏ a : Fin r, t a ^ (2 * lam a) = (∏ a : Fin r, t a ^ lam a) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul, Nat.mul_comm]
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ _ hsupp,
    Formalism.REAL.fischerInner_eq_sum_of_subset f f f.support (Finset.Subset.refl _)]
  simp only [hcoeff, ldiag_term]
  simp only [ldiag_term0, Complex.re_sum, Complex.ofReal_re]
  rw [hq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hP0 : 0 ≤ ∏ a : Fin r, t a ^ rowDeg m a :=
    Finset.prod_nonneg fun a _ => pow_nonneg (ht0 a) _
  have hPle := h r t (rowDeg m) lam ht0 ht (hdom m hm) (hsum m hm)
  exact mul_sq_mul_le_sq_mul_mul_of_le (Complex.normSq_nonneg _) (Nat.cast_nonneg _) hP0 hPle

end Formalism.GradedWeylDivisibility
end
end
