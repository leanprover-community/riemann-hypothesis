import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC.CoreC.G

variable {τ : Type} [Fintype τ] [DecidableEq τ]

def gf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * w s

variable (w : (τ →₀ ℕ) → ℂ)

theorem gf_eq (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S) (hq : q.support ⊆ S) :
    gf w p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * w s := by
  unfold gf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem gf_add_left (p p' q : MvPolynomial τ ℂ) : gf w (p + p') q = gf w p q + gf w p' q := by
  classical
  have h1 := support_add (p := p) (q := p')
  rw [gf_eq w (p.support ∪ p'.support ∪ q.support) (h1.trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_left).trans Finset.subset_union_left)
      Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_right).trans Finset.subset_union_left)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_add, star_add]; ring

theorem gf_add_right (p q q' : MvPolynomial τ ℂ) : gf w p (q + q') = gf w p q + gf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_add]; ring

theorem gf_smul_left (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w (r • p) q = star r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) ((MvPolynomial.support_smul).trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_smul, star_mul]; ring

theorem gf_smul_right (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w p (r • q) = r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) Finset.subset_union_left ((MvPolynomial.support_smul).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_smul]; ring

theorem gf_neg_left (p q : MvPolynomial τ ℂ) : gf w (-p) q = -gf w p q := by
  rw [show -p = (-1 : ℂ) • p by simp, gf_smul_left]; simp

theorem gf_neg_right (p q : MvPolynomial τ ℂ) : gf w p (-q) = -gf w p q := by
  rw [show -q = (-1 : ℂ) • q by simp, gf_smul_right]; simp

theorem gf_sub_left (p p' q : MvPolynomial τ ℂ) : gf w (p - p') q = gf w p q - gf w p' q := by
  rw [sub_eq_add_neg, gf_add_left, gf_neg_left, ← sub_eq_add_neg]

theorem gf_sub_right (p q q' : MvPolynomial τ ℂ) : gf w p (q - q') = gf w p q - gf w p q' := by
  rw [sub_eq_add_neg, gf_add_right, gf_neg_right, ← sub_eq_add_neg]

theorem gf_sum_left {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    gf w (∑ i ∈ I, f i) q = ∑ i ∈ I, gf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_left, ih, Finset.sum_insert ha]

theorem gf_sum_right {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    gf w p (∑ i ∈ I, f i) = ∑ i ∈ I, gf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_right, ih, Finset.sum_insert ha]

theorem gf_monomial (s t : τ →₀ ℕ) (a b : ℂ) :
    gf w (monomial s a) (monomial t b) = if s = t then star a * b * w s else 0 := by
  classical
  rw [gf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]

theorem gf_induction {P : MvPolynomial τ ℂ → MvPolynomial τ ℂ → Prop}
    (hm : ∀ s t (a b : ℂ), P (monomial s a) (monomial t b))
    (hl : ∀ p p' q, P p q → P p' q → P (p + p') q) (hr : ∀ p q q', P p q → P p q' → P p (q + q')) :
    ∀ p q, P p q := by
  intro p q
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    induction q using MvPolynomial.induction_on' with
    | monomial t b => exact hm s t a b
    | add q q' h1 h2 => exact hr _ _ _ h1 h2
  | add p p' h1 h2 => exact hl _ _ _ h1 h2

variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw

theorem gf_X_mul (k : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * p) q = κ * gf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [if_pos h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [mul_add, gf_add_left, gf_add_left, h1, h2, mul_add]
  · rw [gf_add_right, map_add, gf_add_right, h1, h2, mul_add]

theorem gf_pderiv (k : τ) (p q : MvPolynomial τ ℂ) : κ * gf w (pderiv k p) q = gf w p (X k * q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : s = Finsupp.single k 1 + t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _), hw, add_tsub_cancel_left]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, star_mul]
      push_cast
      simp only [Complex.star_def, Complex.conj_natCast, map_add, map_one]
      ring
    · rw [if_neg h]
      by_cases h' : s - Finsupp.single k 1 = t
      · rw [if_pos h']
        have : s k = 0 := by
          by_contra h0
          apply h
          rw [← h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [map_add, gf_add_left, gf_add_left, ← h1, ← h2, mul_add]
  · rw [gf_add_right, mul_add, mul_add, gf_add_right, h1, h2]

theorem gf_adj (k l : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * pderiv l p) q = gf w p (X l * pderiv k q) := by
  rw [gf_X_mul κ hw, gf_pderiv κ hw]

omit hw

variable (w) in
theorem gf_herm (hs : ∀ s, star (w s) = w s) (p q : MvPolynomial τ ℂ) : gf w q p = star (gf w p q) := by
  unfold gf
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_mul, star_mul, star_star, hs]; ring

variable (w) in
theorem gf_pos (hs : ∀ s, star (w s) = w s) (hp : ∀ s, 0 < (w s).re) (p : MvPolynomial τ ℂ) (h : p ≠ 0) :
    0 < (gf w p p).re := by
  unfold gf
  rw [Finset.union_self, Complex.re_sum]
  obtain ⟨s, hs0⟩ := (MvPolynomial.ne_zero_iff).mp h
  have hmem : s ∈ p.support := MvPolynomial.mem_support_iff.mpr hs0
  have key : ∀ t, (star (p.coeff t) * p.coeff t * w t).re = Complex.normSq (p.coeff t) * (w t).re := by
    intro t
    have hw' : (w t).im = 0 := by
      have := congrArg Complex.im (hs t); simp at this; linarith
    rw [show star (p.coeff t) * p.coeff t = (Complex.normSq (p.coeff t) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl]
    simp [Complex.mul_re, hw']
  refine Finset.sum_pos' (fun t _ => ?_) ⟨s, hmem, ?_⟩
  · rw [key]; exact mul_nonneg (Complex.normSq_nonneg _) (hp t).le
  · rw [key]; exact mul_pos (Complex.normSq_pos.mpr hs0) (hp s)

omit [Fintype τ] in
theorem pderiv_X' (v u : τ) : pderiv v (X u : MvPolynomial τ ℂ) = if v = u then 1 else 0 := by
  rw [pderiv_X]; by_cases h : v = u
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h, h]

theorem der_expand (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, D (X v) * pderiv v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p u hp =>
    rw [Derivation.leibniz, hp]
    simp only [smul_eq_mul, Derivation.leibniz, pderiv_X', mul_add, Finset.sum_add_distrib]
    have h1 : ∑ v, D (X v) * (p * (if v = u then (1 : MvPolynomial τ ℂ) else 0)) = p * D (X u) := by
      simp [mul_ite]; ring
    have h2 : ∑ v, D (X v) * (X u * pderiv v p) = X u * ∑ v, D (X v) * pderiv v p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1, h2]

theorem der_expand2 (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, ∑ u, (D (X v)).coeff (Finsupp.single u 1) • (X u * pderiv v p) := by
  rw [der_expand D p]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => rw [hlin v]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_mul_assoc]

theorem der_adj {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (D D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u)
    (hlin' : ∀ v, D' (X v) = ∑ u, (D' (X v)).coeff (Finsupp.single u 1) • X u)
    (htr : ∀ v u, (D' (X u)).coeff (Finsupp.single v 1) = star ((D (X v)).coeff (Finsupp.single u 1)))
    (p q : MvPolynomial τ ℂ) : gf w (D p) q = gf w p (D' q) := by
  rw [der_expand2 D hlin p, der_expand2 D' hlin' q]
  simp_rw [gf_sum_left, gf_sum_right, gf_smul_left, gf_smul_right, gf_adj κ hw, htr]
  rw [Finset.sum_comm]

def bf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, p.coeff s * q.coeff s * w s

theorem bf_eq (w : (τ →₀ ℕ) → ℂ) (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S)
    (hq : q.support ⊆ S) : bf w p q = ∑ s ∈ S, p.coeff s * q.coeff s * w s := by
  unfold bf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem bf_add_left (w : (τ →₀ ℕ) → ℂ) (p p' q : MvPolynomial τ ℂ) : bf w (p + p') q = bf w p q + bf w p' q := by
  classical
  have h1 := support_add (p := p) (q := p')
  rw [bf_eq w (p.support ∪ p'.support ∪ q.support) (h1.trans Finset.subset_union_left) Finset.subset_union_right,
    bf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_left).trans Finset.subset_union_left)
      Finset.subset_union_right,
    bf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_right).trans Finset.subset_union_left)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_add]; ring

theorem bf_add_right (w : (τ →₀ ℕ) → ℂ) (p q q' : MvPolynomial τ ℂ) : bf w p (q + q') = bf w p q + bf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_add]; ring

theorem bf_monomial (w : (τ →₀ ℕ) → ℂ) (s t : τ →₀ ℕ) (a b : ℂ) :
    bf w (monomial s a) (monomial t b) = if s = t then a * b * w s else 0 := by
  classical
  rw [bf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]

theorem bf_X_mul {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : bf w (X k * p) q = κ * bf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, bf_monomial, bf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [if_pos h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [mul_add, bf_add_left, bf_add_left, h1, h2, mul_add]
  · rw [bf_add_right, map_add, bf_add_right, h1, h2, mul_add]

theorem bf_pderiv {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : κ * bf w (pderiv k p) q = bf w p (X k * q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, bf_monomial, bf_monomial]
    by_cases h : s = Finsupp.single k 1 + t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _), hw, add_tsub_cancel_left]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s - Finsupp.single k 1 = t
      · rw [if_pos h']
        have : s k = 0 := by
          by_contra h0
          apply h
          rw [← h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [map_add, bf_add_left, bf_add_left, ← h1, ← h2, mul_add]
  · rw [bf_add_right, mul_add, mul_add, bf_add_right, h1, h2]

theorem bf_sum_left (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    bf w (∑ i ∈ I, f i) q = ∑ i ∈ I, bf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bf]
  | insert a I ha ih => rw [Finset.sum_insert ha, bf_add_left, ih, Finset.sum_insert ha]

theorem bf_sum_right (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    bf w p (∑ i ∈ I, f i) = ∑ i ∈ I, bf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bf]
  | insert a I ha ih => rw [Finset.sum_insert ha, bf_add_right, ih, Finset.sum_insert ha]

end PositivityTheory.Rg.Sw.LC.CoreC.G
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem fform_eq_gf (c : ℝ) (p q : PX m n) : fform c p q = gf (fun s => (wt c s : ℂ)) p q := rfl

theorem wt_univ (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    wt c s = ∏ k, ((s k).factorial : ℝ) * (2 * c) ^ (s k) := by
  unfold wt
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : s k = 0 := by simpa [Finsupp.mem_support_iff] using hk
  simp [this]

theorem wt_pos {c : ℝ} (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) : 0 < wt c s := by
  rw [wt_univ]
  exact Finset.prod_pos fun k _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by linarith) _)

theorem wt_step (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by
  have h : wt c (Finsupp.single k 1 + s) = (2 * c) * ((s k : ℝ) + 1) * wt c s := by
    rw [wt_univ, wt_univ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((s j).factorial : ℝ) * (2 * c) ^ (s j)) (Finset.mem_univ k)]
    have hrest : ∏ j ∈ Finset.univ.erase k, (((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j).factorial : ℝ) *
          (2 * c) ^ ((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j) =
        ∏ j ∈ Finset.univ.erase k, ((s j).factorial : ℝ) * (2 * c) ^ (s j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [Finsupp.single_apply, Ne.symm hjk]
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm 1 (s k), Nat.factorial_succ, pow_succ]
    push_cast; ring
  rw [h]; push_cast; ring

theorem KopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) p := by
  simp [KopL, LinearMap.sub_apply, LinearMap.sum_apply]

theorem rdeg_add (ε : Fin m → Bool) (s t : Fin m × Fin n × Bool →₀ ℕ) : rdeg ε (s + t) = rdeg ε s + rdeg ε t := by
  funext a; simp [rdeg, Finset.sum_add_distrib]

theorem rdeg_single (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by
  funext a
  unfold rdeg
  obtain ⟨a0, i0, b0⟩ := k
  simp only [inF1] at hk
  subst hk
  by_cases ha : a = a0
  · subst ha
    rw [if_pos rfl, Finset.sum_eq_single i0]
    · simp
    · intro i _ hi; simp [Finsupp.single_apply, Ne.symm hi]
    · simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ha (congrArg Prod.fst h).symm

theorem term_mem_box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : s l = 0
  · simp [h0]
  · rw [show (monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) ((s l : ℕ) : ℂ) : PX m n) =
        ((s l : ℕ) : ℂ) • monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k' hk' => ?_, ?_, rfl⟩)
    · rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h; rw [h]; exact hk
      · exact hs k' (Finsupp.support_tsub h)
    · have hle : Finsupp.single l 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have e1 : rdeg ε (Finsupp.single k 1) = rdeg ε (Finsupp.single l 1) := by
        rw [rdeg_single ε k hk, rdeg_single ε l hl, hkl]
      rw [rdeg_add, e1, ← rdeg_add, add_tsub_cancel_of_le hle]
      exact hR

theorem gen_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [KopL_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun a ha => ?_) (Submodule.sum_mem _ fun a ha => ?_)
  · have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, i, false) (a, j, false) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
  · have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, j, true) (a, i, true) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR

theorem box_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, KopL ε i j f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => KopL ε i j x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    exact gen_stable ε i j R s hs hR
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

def symW (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℂ := ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem symW_step (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (k) :
    symW (Finsupp.single k 1 + u) = 1 * ((u k : ℂ) + 1) * symW u := by
  have hu : ∀ v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ,
      symW v = ∏ k, ((v k).factorial : ℂ) := fun v => by
    unfold symW
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have : v k = 0 := by simpa [Finsupp.mem_support_iff] using hk
    simp [this]
  rw [hu, hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((u j).factorial : ℂ)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k,
      (((Finsupp.single k 1 + u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) j).factorial : ℂ) =
      ∏ j ∈ Finset.univ.erase k, ((u j).factorial : ℂ) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Finsupp.single_apply, Ne.symm hjk]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (u k), Nat.factorial_succ]
  push_cast; ring

theorem coeff_smul_X {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by
  rw [coeff_smul, coeff_X']
  by_cases h : w0 = u
  · subst h; simp
  · rw [if_neg (fun e => h ((Finsupp.single_left_inj one_ne_zero).mp e)), if_neg h]; simp

theorem expand_lin {τ : Type} [Fintype τ] [DecidableEq τ] (c : ℂ) (w0 : τ) :
    (c • X w0 : MvPolynomial τ ℂ) = ∑ u, (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) • X u := by
  simp_rw [coeff_smul_X, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

theorem symK_lin (ε : Fin m → Bool) (i j : Fin n) (v) :
    ∃ (c : ℂ) (w0 : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)), symK ε i j (X v : Sym m n) = c • X w0 := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;>
    first
    | exact ⟨1, _, (one_smul _ _).symm⟩
    | exact ⟨-1, _, by rw [neg_smul, one_smul]⟩
    | exact ⟨0, Sum.inl (a, i', b), (zero_smul _ _).symm⟩

theorem symK_hlin (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by
  obtain ⟨c, w0, h⟩ := symK_lin ε i j v
  rw [h]; exact expand_lin c w0

theorem symK_tr (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> rcases u with ⟨a', i'', b'⟩ | ⟨a', i'', b'⟩ <;>
    simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp_all [coeff_X', Finsupp.single_left_inj, coeff_neg] <;> aesop

end CoreC

open CoreC CoreC.G in
theorem formFacts : FormFacts := by
  intro m n ε c hc
  have hw : ∀ (s : Fin m × Fin n × Bool →₀ ℕ) k, (fun s => (wt c s : ℂ)) (Finsupp.single k 1 + s) =
      ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (fun s => (wt c s : ℂ)) s := fun s k => wt_step c s k
  have hst : ∀ s : Fin m × Fin n × Bool →₀ ℕ, star ((fun s => (wt c s : ℂ)) s) = (fun s => (wt c s : ℂ)) s :=
    fun s => Complex.conj_ofReal _
  have hpos : ∀ s : Fin m × Fin n × Bool →₀ ℕ, 0 < ((fun s => (wt c s : ℂ)) s).re := fun s => by
    simpa using wt_pos hc s
  refine ⟨fun p q => gf_herm _ hst p q, fun p hp => gf_pos _ hst hpos p hp, fun i j p q => ?_,
    fun i j R f hf => box_stable ε i j R f hf, fun i j s t => ⟨by simp [fform], ?_⟩⟩
  · rw [fform_eq_gf, fform_eq_gf, KopL_apply, KopL_apply, gf_sub_left, gf_sub_right, gf_sum_left, gf_sum_left,
      gf_sum_right, gf_sum_right]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => gf_adj _ hw _ _ _ _
  · exact der_adj (w := symW) 1 symW_step (symK ε i j) (symK ε j i) (symK_hlin ε i j) (symK_hlin ε j i)
      (symK_tr ε i j) s t

end PositivityTheory.Rg.Sw.LC
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool) where
  toFun k := (k.1, k.2.1, !k.2.2)
  invFun k := (k.1, k.2.1, !k.2.2)
  left_inv k := by simp
  right_inv k := by simp

@[simp] theorem pE_apply (k : Fin m × Fin n × Bool) : pE k = (k.1, k.2.1, !k.2.2) := rfl

@[simp] theorem pE_pE (k : Fin m × Fin n × Bool) : pE (pE k) = k := by simp

theorem pE_symm : (pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool)).symm = pE := rfl

theorem first_family_partner_iff (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : inF1 ε (pE k) ↔ ¬ inF1 ε k := by
  obtain ⟨a, i, b⟩ := k; simp only [pE_apply, inF1]; cases b <;> cases ε a <;> simp

theorem mem_first_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by
  unfold F1
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

theorem mem_second_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F2 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, ¬ inF1 ε k := by
  unfold F2
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

theorem pderiv_mem_supported (S : Set (Fin m × Fin n × Bool)) (k) {p : PX m n} (hp : p ∈ supported ℂ S) :
    pderiv k p ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    rw [pderiv_X]
    by_cases h : k = j
    · subst h; simp [Subalgebra.one_mem]
    · simp [Pi.single_apply, Ne.symm h, h]
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hx') hy)
      (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hy') hx)

theorem partial_deriv_mem_first_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p ∈ F1 ε :=
  pderiv_mem_supported _ k hp

theorem partial_deriv_mem_second_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p ∈ F2 ε :=
  pderiv_mem_supported _ k hp

theorem variable_mul_mem_first_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : X k * p ∈ F1 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem variable_mul_mem_second_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : X k * p ∈ F2 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem partial_deriv_zero_first_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact hk ((mem_first_family_iff ε p).mp hp s hs k hks)

theorem partial_deriv_zero_second_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact (mem_second_family_iff ε p).mp hp s hs k hks hk

def piC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false)))

def Bal (s : Fin m × Fin n × Bool →₀ ℕ) : Prop := ∀ a i, s (a, i, false) = s (a, i, true)

instance (s : Fin m × Fin n × Bool →₀ ℕ) : Decidable (Bal s) := by unfold Bal; infer_instance

theorem contr_eqS (c : ℝ) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) {p : PX m n} (hp : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, if Bal s then p.coeff s * piC c s else 0 := by
  unfold contr
  refine Finset.sum_subset hp fun s _ hs => ?_
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eqS c (p.support ∪ q.support) MvPolynomial.support_add, contr_eqS c (p.support ∪ q.support) Finset.subset_union_left,
    contr_eqS c (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eqS c p.support MvPolynomial.support_smul, contr_eqS c p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_smul, mul_assoc]

theorem contr_sum (c : ℝ) {ι : Type} (I : Finset ι) (f : ι → PX m n) : contr c (∑ i ∈ I, f i) = ∑ i ∈ I, contr c (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [contr]
  | insert a I ha ih => rw [Finset.sum_insert ha, contr_add, ih, Finset.sum_insert ha]

theorem contr_neg (c : ℝ) (p : PX m n) : contr c (-p) = -contr c p := by
  rw [show -p = (-1 : ℂ) • p by simp, contr_smul]; ring

theorem contr_sub (c : ℝ) (p q : PX m n) : contr c (p - q) = contr c p - contr c q := by
  rw [sub_eq_add_neg, contr_add, contr_neg]; ring

theorem contr_monomial (c : ℝ) (v : Fin m × Fin n × Bool →₀ ℕ) (d : ℂ) :
    contr c (monomial v d) = if Bal v then d * piC c v else 0 := by
  classical
  rw [contr_eqS c {v} ((support_monomial_subset).trans (by simp)), Finset.sum_singleton]
  simp [coeff_monomial]

theorem bal_iff (ε : Fin m → Bool) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) : Bal (s + u) ↔ s = u.mapDomain pE := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  constructor
  · intro hb
    ext ⟨a, i, b⟩
    rw [Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]
    have hb' := hb a i
    simp only [Finsupp.add_apply] at hb'
    cases b <;> cases hεa : ε a
    · have h1 := hs0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
    · have h1 := hs0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
  · intro h a i
    rw [h]
    simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
    ring

theorem piC_eq_wt (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ}
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (h : s = u.mapDomain pE) : piC c (s + u) = (wt c s : ℂ) := by
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  rw [wt_univ]
  push_cast
  rw [Fintype.prod_prod_type]
  unfold piC
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  subst h
  simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
  cases hεa : ε a
  · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
    rw [h1]; simp
  · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
    rw [h1]; simp [mul_comm]

theorem contr_mono (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (a b : ℂ) :
    contr c (monomial s a * monomial u b) = if s = u.mapDomain pE then a * b * (wt c s : ℂ) else 0 := by
  rw [monomial_mul, contr_monomial]
  by_cases h : s = u.mapDomain pE
  · rw [if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]
  · rw [if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]

theorem contr_eq_bf (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by
  conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]
  conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [contr_sum, bf_sum_right]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]

theorem T1 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by
  rw [contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]
  congr 2
  have := pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g
  rw [pE_pE] at this
  exact this

theorem T2 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) * contr c (pderiv k h * g) = contr c (h * (X (pE k) * g)) := by
  rw [contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg,
    contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]
  congr 1
  rw [map_mul, rename_X, pE_pE]

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem tA (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * pderiv (b, i, false) h * g) = contr c (h * (X (b, i, true) * pderiv (a, i, true) g)) := by
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (partial_deriv_mem_first_family ε (b, i, false) hh) hg
  have h2 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false] at h1 h2
  rw [h1, h2]

theorem tB (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (b, i, true) * pderiv (a, i, true) h * g) = contr c (h * (X (a, i, false) * pderiv (b, i, false) g)) := by
  have h1 := T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)
  simp only [pE_apply, Bool.not_true] at h1 h2
  rw [h1, h2]

theorem tC (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * X (b, i, true) * h * g) =
      ((2 * c : ℝ) : ℂ) ^ 2 * contr c (h * pderiv (b, i, false) (pderiv (a, i, true) g)) := by
  have hbT : inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (variable_mul_mem_first_family ε hbT hh) hg
  have h2 := T1 ε (c := c) (k := (b, i, true)) hbT hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [mul_assoc (X (a, i, false)), h1, h2]; ring

theorem tD (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by
  have hbT : ¬ inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [pow_two, mul_assoc, h1, h2, mul_assoc]

theorem contraction_first_operator_adjoint (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (a b : Fin m) {h g : PX m n} (hh : h ∈ F1 ε)
    (hg : g ∈ F2 ε) : contr c (D1 ε c a b h * g) = -contr c (h * D2 ε c a b g) := by
  have hc2 : ((2 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
  unfold D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]
      exact Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      rw [neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg
  · rw [if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [← tD ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [tC ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem dop_split (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) :
    Dop ε c a b (f * g) = D1 ε c a b f * g + f * D2 ε c a b g := by
  have hL : ∀ k, pderiv k (f * g) = f * pderiv k g + g * pderiv k f := fun k => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hL2 : ∀ k (p q : PX m n), pderiv k (p * q) = p * pderiv k q + q * pderiv k p := fun k p q => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold Dop D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf]
      ring
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      ring
  · rw [if_neg hab, if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, map_add, hL2 _ f, hL2 _ g, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      simp only [mul_zero, zero_add, add_zero, zero_mul, map_zero, smul_eq_C_mul]
      ring
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf, mul_zero, add_zero, hL2 _ f,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf, mul_zero, add_zero]
      simp only [smul_eq_C_mul]
      ring

theorem X_pderiv_mono (k : Fin m × Fin n × Bool) (v : Fin m × Fin n × Bool →₀ ℕ) :
    (X k * pderiv k (monomial v (1 : ℂ)) : PX m n) = ((v k : ℕ) : ℂ) • monomial v 1 := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : v k = 0
  · simp [h0]
  · rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)), smul_monomial, smul_eq_mul,
      mul_one]

theorem centre (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k)
    (hr : rdeg ε s ≠ rdeg ε (u.mapDomain pE)) : Λ (monomial s 1 * monomial u 1) = 0 := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hr
  rw [monomial_mul, one_mul]
  have hD : Dop ε c a a (monomial (s + u) (1 : ℂ)) =
      ((∑ i, ((s + u) (a, i, true) : ℂ)) - ∑ i, ((s + u) (a, i, false) : ℂ)) • monomial (s + u) 1 := by
    unfold Dop
    rw [if_pos rfl]
    simp only [X_pderiv_mono, ← Finset.sum_sub_distrib, Finset.sum_smul, sub_smul]
  have h0 := hΛ a a (monomial (s + u) 1)
  rw [hD, map_smul, smul_eq_mul] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  simp only [rdeg, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_not] at ha
  rw [← ne_eq, sub_ne_zero]
  simp only [Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  cases hεa : ε a
  · have e1 : ∀ i, u (a, i, true) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, false) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_false] at ha
    intro h; apply ha; exact_mod_cast h
  · have e1 : ∀ i, u (a, i, false) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, true) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_true] at ha
    intro h; apply ha; exact_mod_cast h.symm

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def cand (ε : Fin m → Bool) (r : Fin m → ℕ) : Finset (Fin m × Fin n × Bool →₀ ℕ) :=
  ((Fintype.piFinset fun _ : Fin m × Fin n × Bool => Finset.range (∑ a, r a + 1)).image
    Finsupp.equivFunOnFinite.symm).filter (fun t => (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r)

theorem le_rdeg (ε : Fin m → Bool) (t : Fin m × Fin n × Bool →₀ ℕ) (k) (hk : inF1 ε k) : t k ≤ rdeg ε t k.1 := by
  obtain ⟨a, i, b⟩ := k
  simp only [inF1] at hk
  subst hk
  unfold rdeg
  exact Finset.single_le_sum (f := fun i' => t (a, i', !ε a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem mem_cand (ε : Fin m → Bool) (r : Fin m → ℕ) (t : Fin m × Fin n × Bool →₀ ℕ) :
    t ∈ cand ε r ↔ (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r := by
  unfold cand
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨⇑t, ?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : inF1 ε k
  · calc t k ≤ rdeg ε t k.1 := le_rdeg ε t k hk
      _ = r k.1 := by rw [h.2]
      _ ≤ ∑ a, r a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · have : t k = 0 := by
      by_contra h0; exact hk (h.1 k (Finsupp.mem_support_iff.mpr h0))
    rw [this]; exact Nat.zero_le _

def Bm (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  if ∀ k ∈ s.support, inF1 ε k then
    ∑ t ∈ cand ε (rdeg ε s), (Λ (monomial s 1 * monomial (t.mapDomain pE) 1) / (wt c t : ℂ)) • monomial t 1
  else 0

def Bop (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) : Module.End ℂ (PX m n) :=
  (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr ℂ (Bm ε c Λ)

theorem Bop_mono (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    Bop ε c Λ (monomial s 1) = Bm ε c Λ s := by
  have := (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr_basis ℂ (Bm ε c Λ) s
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem as_sum' (p : PX m n) : p = ∑ s ∈ p.support, p.coeff s • monomial s (1 : ℂ) := by
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem monomial_mem_first_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F1 ε := by
  rw [mem_first_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, if_neg (Ne.symm h)])
  subst this; exact ht

theorem monomial_mem_second_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, ¬ inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F2 ε := by
  rw [mem_second_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, if_neg (Ne.symm h)])
  subst this; exact ht

theorem representing_monomial_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s) : Bm ε c Λ s ∈ F1 ε := by
  unfold Bm
  split_ifs
  · exact Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (monomial_mem_first_family ε ((mem_cand ε _ t).mp ht).1 1)
  · exact Submodule.zero_mem _

theorem representing_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (p : PX m n) : Bop ε c Λ p ∈ F1 ε := by
  rw [as_sum' p, map_sum]
  exact Submodule.sum_mem _ fun s _ => by rw [map_smul, Bop_mono]; exact Submodule.smul_mem _ _ (representing_monomial_mem_first_family ε c Λ s)

theorem mapDomain_pE_pE (u : Fin m × Fin n × Bool →₀ ℕ) : (u.mapDomain pE).mapDomain pE = u := by
  ext k; simp [Finsupp.mapDomain_equiv_apply, pE_symm]

theorem partner_support_first_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff, not_not] at this

theorem partner_support_second_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, ¬ inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff] at this

theorem key_mono (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    Λ (monomial s 1 * monomial u 1) = contr c (Bm ε c Λ s * monomial u 1) := by
  unfold Bm
  rw [if_pos hs, Finset.sum_mul, contr_sum]
  simp_rw [smul_mul_assoc, contr_smul]
  have e : ∀ t ∈ cand ε (rdeg ε s), contr c (monomial t 1 * monomial u 1) =
      if t = u.mapDomain pE then (wt c t : ℂ) else 0 := fun t ht => by
    rw [contr_mono ε c ((mem_cand ε _ t).mp ht).1 hu]; simp
  rw [Finset.sum_congr rfl fun t ht => by rw [e t ht]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rw [mapDomain_pE_pE, div_mul_cancel₀]
    exact_mod_cast (wt_pos hc _).ne'
  · refine centre ε c Λ hΛ hs hu fun h => hmem ?_
    rw [mem_cand]; exact ⟨partner_support_first_family ε hu, h.symm⟩

theorem functional_representation_by_contraction (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) : Λ (f * g) = contr c (Bop ε c Λ f * g) := by
  conv_lhs => rw [as_sum' f, as_sum' g, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [as_sum' f, map_sum, as_sum' g, Finset.sum_mul_sum, contr_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [map_sum, contr_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, Bop_mono, smul_mul_smul_comm, map_smul, smul_mul_smul_comm, contr_smul,
    key_mono ε hc Λ hΛ ((mem_first_family_iff ε f).mp hf s hs) ((mem_second_family_iff ε g).mp hg u hu), smul_eq_mul]

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem first_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f : PX m n} (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  unfold D1
  split_ifs with hab ha ha
  · refine (F1 ε).neg_mem ((F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ha]) (partial_deriv_mem_first_family ε _ hf))
  · exact (F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ← hab]; simpa using ha) (partial_deriv_mem_first_family ε _ hf)
  · have hb : ε b = false := by cases h' : ε b <;> simp_all
    refine (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_first_family ε (by simp [inF1, ha]) (variable_mul_mem_first_family ε (by simp [inF1, hb]) hf)
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    exact (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => partial_deriv_mem_first_family ε _ (partial_deriv_mem_first_family ε _ hf))

theorem second_operator_mem_second_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {g : PX m n} (hg : g ∈ F2 ε) : D2 ε c a b g ∈ F2 ε := by
  unfold D2
  split_ifs with hab ha ha
  · exact (F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1, ← hab, ha]) (partial_deriv_mem_second_family ε _ hg)
  · refine (F2 ε).neg_mem ((F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha)
      (partial_deriv_mem_second_family ε _ hg))
  · exact (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => partial_deriv_mem_second_family ε _ (partial_deriv_mem_second_family ε _ hg))
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    refine (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha) (variable_mul_mem_second_family ε (by simp [inF1, hb]) hg)

theorem bf_mono_right (w : (Fin m × Fin n × Bool →₀ ℕ) → ℂ) (p : PX m n) (t : Fin m × Fin n × Bool →₀ ℕ) :
    bf w p (monomial t 1) = p.coeff t * w t := by
  classical
  rw [bf_eq w (p.support ∪ {t}) Finset.subset_union_left ((support_monomial_subset).trans Finset.subset_union_right)]
  rw [Finset.sum_eq_single t]
  · simp [coeff_monomial]
  · intro s _ hs; simp [coeff_monomial, Ne.symm hs]
  · intro h; simp [coeff_monomial]; left; by_contra h'; exact h (Finset.mem_union_left _
      (MvPolynomial.mem_support_iff.mpr h'))

theorem nondeg (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by
  ext s
  rw [coeff_zero]
  by_cases hs : ∀ k ∈ s.support, inF1 ε k
  · have hu := partner_support_second_family ε hs
    have := h0 (s.mapDomain pE) hu
    rw [contr_eq_bf ε c hh (monomial_mem_second_family ε hu 1), rename_monomial, mapDomain_pE_pE, bf_mono_right] at this
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (wt_pos hc s).ne')
  · by_contra hne
    exact hs ((mem_first_family_iff ε h).mp hh s (MvPolynomial.mem_support_iff.mpr hne))

theorem Bop_box (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, Bop ε c Λ f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => Bop ε c Λ x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    rw [Bop_mono]
    unfold Bm
    rw [if_pos hs]
    refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨htF, htr⟩ := (mem_cand ε _ t).mp ht
    exact ⟨t, htF, by rw [htr]; exact hR, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

end CoreC

open CoreC in
theorem repB : RepB := by
  intro m n ε c hc Λ hΛ
  refine ⟨Bop ε c Λ, fun R f hf => Bop_box ε c Λ R f hf, fun f hf g hg => functional_representation_by_contraction ε hc Λ hΛ hf hg, ?_⟩
  intro a b f hf
  have hB1 : Bop ε c Λ (D1 ε c a b f) ∈ F1 ε := representing_operator_mem_first_family ε c Λ _
  have hB2 : D1 ε c a b (Bop ε c Λ f) ∈ F1 ε := first_operator_mem_first_family ε c a b (representing_operator_mem_first_family ε c Λ f)
  rw [← sub_eq_zero]
  refine nondeg ε hc (Submodule.sub_mem _ hB1 hB2) fun u hu => ?_
  have hg : (monomial u (1 : ℂ) : PX m n) ∈ F2 ε := monomial_mem_second_family ε hu 1
  rw [sub_mul, contr_sub, ← functional_representation_by_contraction ε hc Λ hΛ (first_operator_mem_first_family ε c a b hf) hg,
    contraction_first_operator_adjoint ε hc a b (representing_operator_mem_first_family ε c Λ f) hg, ← functional_representation_by_contraction ε hc Λ hΛ hf (second_operator_mem_second_family ε c a b hg), sub_neg_eq_add,
    ← map_add, ← dop_split ε c a b hf hg, hΛ]

end PositivityTheory.Rg.Sw.LC
end
end
