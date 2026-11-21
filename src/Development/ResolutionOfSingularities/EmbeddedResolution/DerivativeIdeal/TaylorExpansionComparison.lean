import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal

section
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion

section

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

private theorem iterate_deriv_mul_eq_sum_nsmul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ i : ℕ,
        ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g))
          = n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      intro i
      rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        ← Function.iterate_succ_apply' (⇑D) (n - i) g,
        ← Function.iterate_succ_apply' (⇑D) i f,
        mul_comm ((⇑D)^[n - i] g) ((⇑D)^[i + 1] f), smul_add]
    have e3 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)
        = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), zero_smul,
        add_zero]
    have e1 : ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
        = (∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner : ∑ i ∈ Finset.range n,
            n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - (i + 1) + 1] g)
          = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have h := Finset.mem_range.mp hi
        have hi' : n - (i + 1) + 1 = n - i := by omega
        rw [hi']
      rw [Finset.sum_range_succ', inner]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    have e2 : ∑ i ∈ Finset.range (n + 1 + 1),
          (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g)
        = ((∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner2 : ∑ i ∈ Finset.range (n + 1),
            (n + 1).choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n + 1 - (i + 1)] g)
          = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        rw [← e3, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) :=
          Nat.choose_succ_succ n i
        have hs : n + 1 - (i + 1) = n - i := by omega
        rw [hc, hs, add_smul]
      rw [Finset.sum_range_succ', inner2]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    calc (⇑D)^[n + 1] (f * g)
        = ⇑D ((⇑D)^[n] (f * g)) := Function.iterate_succ_apply' _ _ _
      _ = ⇑D (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [ih]
      _ = ∑ i ∈ Finset.range (n + 1), ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [map_sum]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)) :=
            Finset.sum_congr rfl fun i _ => key i
      _ = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g))
            + ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) :=
            Finset.sum_add_distrib
      _ = ∑ i ∈ Finset.range (n + 1 + 1),
            (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g) := by
            rw [e1, e2]; ring

theorem iterate_deriv_mul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  rw [iterate_deriv_mul_eq_sum_nsmul D n f g]
  exact Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

def coeff (σ : R →+* S) (D : Derivation A R R) (i : ℕ) (f : R) : S :=
  algebraMap ℚ S ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f)

def truncatedSeries (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) : S :=
  ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j

@[simp]
theorem truncatedSeries_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) :
    truncatedSeries σ D β N f =
      ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j :=
  rfl

theorem truncatedSeries_of_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) (hf : D f = 0) : truncatedSeries σ D β N f = σ f := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  have key : ∀ k : ℕ, (⇑D)^[k + 1] f = 0 := by
    intro k
    rw [Function.iterate_succ_apply, hf]
    exact Function.iterate_fixed hz k
  rw [truncatedSeries_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [key k]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 0 < N)) h

theorem truncatedSeries_sub_mem_span_singleton (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) :
    truncatedSeries σ D β N f - σ f ∈ Ideal.span ({β} : Set S) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  have key : truncatedSeries σ D β (M + 1) f - σ f =
      ∑ j ∈ Finset.range M,
        algebraMap ℚ S (((j + 1).factorial : ℚ)⁻¹) * σ ((⇑D)^[j + 1] f) * β ^ (j + 1) := by
    rw [truncatedSeries_apply, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Ideal.mem_span_singleton]
  exact dvd_mul_of_dvd_right (dvd_pow_self β j.succ_ne_zero) _

private theorem factorial_inv_mul_choose {S' : Type*} [CommRing S'] [Algebra ℚ S'] (j i : ℕ)
    (h : i ≤ j) :
    algebraMap ℚ S' ((j.factorial : ℚ)⁻¹) * (j.choose i : S')
      = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * algebraMap ℚ S' (((j - i).factorial : ℚ)⁻¹) := by
  have hj : ((j.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  have hi : ((i.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos i).ne'
  have hji : (((j - i).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos (j - i)).ne'
  have h1 : (j.choose i : ℚ) * (i.factorial : ℚ) * ((j - i).factorial : ℚ)
      = (j.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have key : ((j.factorial : ℚ))⁻¹ * (j.choose i : ℚ)
      = ((i.factorial : ℚ))⁻¹ * (((j - i).factorial : ℚ))⁻¹ := by
    field_simp
    linear_combination h1
  have h2 := congrArg (algebraMap ℚ S') key
  simpa only [map_mul, map_natCast] using h2

private theorem coeff_eq {A' R' S' : Type*} [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra ℚ S'] (σ : R' →+* S') (D : Derivation A' R' R') (i : ℕ) (f : R') :
    coeff σ D i f = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f) := rfl

theorem truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f * g) =
      ∑ j ∈ Finset.range N,
        β ^ j * ∑ i ∈ Finset.range (j + 1),
          coeff σ D i f * coeff σ D (j - i) g := by
  rw [truncatedSeries_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_deriv_mul D j f g, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have key := factorial_inv_mul_choose (S' := S) j i hij
  simp only [coeff_eq, map_mul, map_natCast]
  linear_combination (σ ((⇑D)^[i] f) * σ ((⇑D)^[j - i] g) * β ^ j) * key

theorem truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) :
    truncatedSeries σ D β N 0 = 0 := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  rw [truncatedSeries_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Function.iterate_fixed hz j]
  simp

theorem truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f + g) = truncatedSeries σ D β N f + truncatedSeries σ D β N g := by
  have key : ∀ j : ℕ, (⇑D)^[j] (f + g) = (⇑D)^[j] f + (⇑D)^[j] g := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]
  simp only [truncatedSeries_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, map_add]
  ring

theorem truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (hN : 1 ≤ N) :
    truncatedSeries σ D β N 1 = 1 := by
  have h1 : D (1 : R) = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1, map_one]

private theorem sum_range_sum_range_succ_eq_sum_sum_Ico {T : Type*} [AddCommMonoid T] (N : ℕ) (h : ℕ → ℕ → T) :
    ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hL : ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (j + 1), h i j
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j)
          + ∑ i ∈ Finset.range (N + 1), h i N :=
      Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j + 1), h i j) N
    have hR1 : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j)
          + ∑ j ∈ Finset.Ico N (N + 1), h N j :=
      Finset.sum_range_succ (fun i => ∑ j ∈ Finset.Ico i (N + 1), h i j) N
    have hR2 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j)
          + ∑ i ∈ Finset.range N, h i N := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N := le_of_lt (Finset.mem_range.mp hi)
      exact Finset.sum_Ico_succ_top hiN (fun j => h i j)
    have hR3 : ∑ j ∈ Finset.Ico N (N + 1), h N j = h N N := by
      rw [Finset.sum_Ico_succ_top (le_refl N) (fun j => h N j), Finset.Ico_self,
        Finset.sum_empty, zero_add]
    have hlast : ∑ i ∈ Finset.range (N + 1), h i N
        = (∑ i ∈ Finset.range N, h i N) + h N N :=
      Finset.sum_range_succ (fun i => h i N) N
    rw [hL, hR1, hR2, hR3, ih, hlast, add_assoc]

private theorem sum_Ico_mul_pow_eq_sum_range {T : Type*} [CommRing T] (a b : ℕ → T) (β : T) (N i : ℕ) :
    ∑ j ∈ Finset.Ico i N, a i * b (j - i) * β ^ j
      = ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : i + k - i = k := by omega
  simp only [hk]

private theorem sum_convolution_sub_mul_mem {T : Type*} [CommRing T] (β : T) (N : ℕ) (J : Ideal T)
    (hβ : β ^ N ∈ J) (a b : ℕ → T) :
    (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      - (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j) ∈ J := by
  have hprod : (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j)
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have htri : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
    have e1 : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
        = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), a i * b (j - i) * β ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine e1.trans ((sum_range_sum_range_succ_eq_sum_sum_Ico N (fun i j => a i * b (j - i) * β ^ j)).trans ?_)
    exact Finset.sum_congr rfl fun i _ => sum_Ico_mul_pow_eq_sum_range a b β N i
  have hdist : (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k))
      = ∑ i ∈ Finset.range N, ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
          - ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)) := by
    refine (eq_sub_of_add_eq ?_).symm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, htri, hdist]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  have hsplit : ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)
      = (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (N - i)) (Nat.sub_le N i)).symm
  rw [hsplit]
  have hre : (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k))
      = -(∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k)) := by ring
  rw [hre]
  refine neg_mem (Ideal.sum_mem _ fun k hk => ?_)
  have hk1 : N - i ≤ k := (Finset.mem_Ico.mp hk).1
  have hpow : β ^ (i + k) ∈ J := by
    have he : i + k = N + (i + k - N) := by omega
    rw [he, pow_add]
    exact Ideal.mul_mem_right _ _ hβ
  exact Ideal.mul_mem_left _ _ hpow

theorem truncatedSeries_mul_sub_mem (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    truncatedSeries σ D β N (f * g) - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J := by
  have hf : truncatedSeries σ D β N f
      = ∑ j ∈ Finset.range N, coeff σ D j f * β ^ j := rfl
  have hg : truncatedSeries σ D β N g
      = ∑ j ∈ Finset.range N, coeff σ D j g * β ^ j := rfl
  rw [truncatedSeries_mul σ D β N f g, hf, hg]
  exact sum_convolution_sub_mul_mem β N J hβ (fun i => coeff σ D i f)
    (fun i => coeff σ D i g)

private theorem mk_truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hN : 1 ≤ N) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 1) = 1 := by
  have h1 : D 1 = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1]
  simp

private theorem mk_truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) *
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  have h : truncatedSeries σ D β N (f * g)
      - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J :=
    truncatedSeries_mul_sub_mem σ D β N J hβ f g
  have h2 : Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g))
      = Ideal.Quotient.mk J (truncatedSeries σ D β N f * truncatedSeries σ D β N g) :=
    Ideal.Quotient.eq.mpr h
  rw [h2, map_mul]

private theorem mk_truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 0) = 0 := by
  rw [truncatedSeries_zero, map_zero]

private theorem mk_truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f + g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) +
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  rw [truncatedSeries_add, map_add]

def truncatedSeriesRingHom (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) : R →+* S ⧸ J :=
  { toFun := fun f => Ideal.Quotient.mk J (truncatedSeries σ D β N f)
    map_one' := mk_truncatedSeries_one σ D β N J hN
    map_mul' := mk_truncatedSeries_mul σ D β N J hβ
    map_zero' := mk_truncatedSeries_zero σ D β N J
    map_add' := mk_truncatedSeries_add σ D β N J }

@[simp]
theorem truncatedSeriesRingHom_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) (f : R) :
    truncatedSeriesRingHom σ D β N J hN hβ f = Ideal.Quotient.mk J (truncatedSeries σ D β N f) :=
  rfl

end

end FunctorialResolution.EmbeddedResolution.TaylorExpansion
end

section
namespace FunctorialResolution.EmbeddedResolution

section

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

private theorem exists_mul_deriv_pow_eq_pow_mul {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (Δ : Derivation k S S) (b : S) (n : ℕ) :
    ∃ c : S, b * Δ (b ^ n) = b ^ n * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + Δ b, ?_⟩
      have hbp : b ^ (m + 1) = b * b ^ m := by ring
      have hl : Δ (b * b ^ m) = b * Δ (b ^ m) + b ^ m * Δ b := by
        simp
      rw [hbp, hl]
      linear_combination b * hc

theorem pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (M J : Ideal S) (Δ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ (j : ℕ) (g : S), g ∈ J → b ^ j * (⇑Δ)^[j] g ∈ J := by
  intro j
  induction j with
  | zero =>
      intro g hg
      simpa using hg
  | succ j ih =>
      intro g hg
      have hIH : b ^ j * (⇑Δ)^[j] g ∈ J := ih g hg
      have hkey : b * Δ (b ^ j * (⇑Δ)^[j] g) ∈ J :=
        hMJ (Ideal.mul_mem_mul hb (derivation_apply_mem_derivIdeal k J Δ hIH))
      obtain ⟨c, hc⟩ := exists_mul_deriv_pow_eq_pow_mul Δ b j
      have hleib : Δ (b ^ j * (⇑Δ)^[j] g)
          = b ^ j * Δ ((⇑Δ)^[j] g) + (⇑Δ)^[j] g * Δ (b ^ j) := by
        simp
      have hiter : (⇑Δ)^[j + 1] g = Δ ((⇑Δ)^[j] g) := Function.iterate_succ_apply' (⇑Δ) j g
      have hEq : b ^ (j + 1) * (⇑Δ)^[j + 1] g
          = b * Δ (b ^ j * (⇑Δ)^[j] g) - c * (b ^ j * (⇑Δ)^[j] g) := by
        rw [hiter, hleib]
        linear_combination (-((⇑Δ)^[j] g)) * hc
      rw [hEq]
      exact Submodule.sub_mem J hkey (Ideal.mul_mem_left J c hIH)

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

theorem truncatedSeries_length_one (σ : R →+* S) (D : Derivation A R R) (β : S) (f : R) :
    TaylorExpansion.truncatedSeries σ D β 1 f = σ f := by
  simp [TaylorExpansion.truncatedSeries_apply]

theorem truncatedSeries_of_deriv_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 2 ≤ N) (f : R) (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D β N f = σ f + σ (D f) * β := by
  have h2 : (⇑D)^[2] f = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp [hf]
  have hvan : ∀ j : ℕ, 2 ≤ j → (⇑D)^[j] f = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, Function.iterate_add_apply, h2]
    exact Function.iterate_fixed (by simp) m
  have hsub : Finset.range 2 ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)
  have hsum : ∑ j ∈ Finset.range 2,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j
      = ∑ j ∈ Finset.range N,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j := by
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · exact absurd (Finset.mem_range.mpr h) hj
      · exact h
    rw [hvan j hj2]
    simp
  rw [TaylorExpansion.truncatedSeries_apply, ← hsum]
  simp [Finset.sum_range_succ]

theorem truncatedSeries_mem_map {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra ℚ B] (φ : R →+* B) (D : Derivation A R R) (b : R) (J : Ideal R)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J)
    (N : ℕ) (g : R) (hg : g ∈ J) :
    TaylorExpansion.truncatedSeries φ D (φ b) N g ∈ Ideal.map φ J := by
  rw [TaylorExpansion.truncatedSeries_apply]
  refine Ideal.sum_mem _ fun j _ => ?_
  have h : φ (b ^ j * (⇑D)^[j] g) ∈ Ideal.map φ J :=
    Ideal.mem_map_of_mem φ (hstab j g hg)
  rw [map_mul, map_pow] at h
  have h2 := Ideal.mul_mem_left (Ideal.map φ J) (algebraMap ℚ B ((j.factorial : ℚ)⁻¹)) h
  have h3 : algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * φ ((⇑D)^[j] g) * φ b ^ j
      = algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * (φ b ^ j * φ ((⇑D)^[j] g)) := by
    ring
  rw [h3]
  exact h2

end

section

open IsLocalRing

def IsTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : P,
    TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x) ∈ maximalIdeal B ^ N

theorem isTaylorExpansionOn_mvPolynomial {k : Type*} [CommRing k] {ι : Type*}
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hβ : β ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      φ (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) =
        φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = 0)
    (hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) -
          φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) φ φ' D β := by
  intro N hN x
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have key :
      (TaylorExpansion.truncatedSeriesRingHom φ D β N (maximalIdeal B ^ N) hN hβN).comp
          (algebraMap (MvPolynomial ι k) R) =
        ((Ideal.Quotient.mk (maximalIdeal B ^ N)).comp φ').comp
          (algebraMap (MvPolynomial ι k) R) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h1 : TaylorExpansion.truncatedSeries φ D β N
            (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c))
          = φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) := by
        rw [TaylorExpansion.truncatedSeries_of_deriv_eq_zero φ D β N hN
          (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) (hDconst c)]
        exact hconst c
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]
      exact Ideal.Quotient.eq.2 (hvar i N hN)
  have h := RingHom.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h
  exact Ideal.Quotient.eq.1 h

private theorem derivation_apply_eq_zero_of_formallyUnramified {P R : Type*} [CommRing P]
    [CommRing R] [Algebra P R] [Algebra.FormallyUnramified P R] {M : Type*} [AddCommGroup M]
    [Module P M] [Module R M] [IsScalarTower P R M] (d : Derivation P R M) (x : R) : d x = 0 := by
  have h0 : KaehlerDifferential.D P R x = 0 := Subsingleton.elim _ _
  have h1 : (Derivation.liftKaehlerDifferential d) (KaehlerDifferential.D P R x) = d x :=
    Derivation.liftKaehlerDifferential_comp_D d x
  rw [h0, map_zero] at h1
  exact h1.symm

private theorem sub_mem_pow_succ_of_sub_mem_pow (P : Type*) {R B : Type*} [CommRing P] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra.FormallyUnramified P R]
    (φ' : R →+* B) (m : Ideal B) (T : R → B) (k : ℕ) (hk : 1 ≤ k)
    (hadd : ∀ x y : R, T (x + y) = T x + T y)
    (hone : T 1 = 1)
    (hmul : ∀ x y : R, T (x * y) - T x * T y ∈ m ^ (k + 1))
    (hP : ∀ x : P, T (algebraMap P R x) - φ' (algebraMap P R x) ∈ m ^ (k + 1))
    (hind : ∀ x : R, T x - φ' x ∈ m ^ k) (x : R) :
    T x - φ' x ∈ m ^ (k + 1) := by
  let _ : Algebra R B := φ'.toAlgebra
  let _ : Algebra P B := (φ'.comp (algebraMap P R)).toAlgebra
  have : IsScalarTower P R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P R (B ⧸ m ^ (k + 1)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hleib : ∀ a b : R,
      T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a)) ∈ m ^ (k + 1) := by
    intro a b
    have h1 : T (a * b) - T a * T b ∈ m ^ (k + 1) := hmul a b
    have h2 : (T a - φ' a) * (T b - φ' b) ∈ m ^ (k + 1) := by
      have h3 : (T a - φ' a) * (T b - φ' b) ∈ m ^ k * m ^ k :=
        Ideal.mul_mem_mul (hind a) (hind b)
      have h4 : m ^ k * m ^ k ≤ m ^ (k + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact h4 h3
    have heq : T (a * b) - φ' (a * b) - (φ' a * (T b - φ' b) + φ' b * (T a - φ' a))
        = T (a * b) - T a * T b + (T a - φ' a) * (T b - φ' b) := by
      rw [map_mul]
      ring
    rw [heq]
    exact Ideal.add_mem _ h1 h2
  let d : Derivation P R (B ⧸ m ^ (k + 1)) :=
    { toFun := fun y => Ideal.Quotient.mk (m ^ (k + 1)) (T y - φ' y)
      map_add' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a + b) - φ' (a + b))
            = Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
              + Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
        have harg : T (a + b) - φ' (a + b) = T a - φ' a + (T b - φ' b) := by
          rw [hadd, map_add]
          ring
        rw [harg, map_add]
      map_smul' := by
        intro p a
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (p • a) - φ' (p • a))
            = p • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : (algebraMap P (B ⧸ m ^ (k + 1))) p
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' (algebraMap P R p)) := rfl
        rw [halg, ← map_mul]
        refine Ideal.Quotient.eq.mpr ?_
        have h1 := hleib (algebraMap P R p) a
        have h2 : φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)) ∈ m ^ (k + 1) :=
          Ideal.mul_mem_left _ _ (hP p)
        have h3 := Ideal.add_mem _ h1 h2
        have heq : T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - (φ' (algebraMap P R p) * (T a - φ' a)
                + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p)))
              + φ' a * (T (algebraMap P R p) - φ' (algebraMap P R p))
            = T (algebraMap P R p * a) - φ' (algebraMap P R p * a)
              - φ' (algebraMap P R p) * (T a - φ' a) := by
          ring
        rw [heq] at h3
        exact h3
      map_one_eq_zero' := by
        show Ideal.Quotient.mk (m ^ (k + 1)) (T 1 - φ' 1) = 0
        rw [hone, map_one, sub_self, map_zero]
      leibniz' := by
        intro a b
        show Ideal.Quotient.mk (m ^ (k + 1)) (T (a * b) - φ' (a * b))
            = a • Ideal.Quotient.mk (m ^ (k + 1)) (T b - φ' b)
              + b • Ideal.Quotient.mk (m ^ (k + 1)) (T a - φ' a)
        simp only [Algebra.smul_def]
        have halg : ∀ y : R, (algebraMap R (B ⧸ m ^ (k + 1))) y
            = Ideal.Quotient.mk (m ^ (k + 1)) (φ' y) := fun _ => rfl
        rw [halg a, halg b, ← map_mul, ← map_mul, ← map_add]
        exact Ideal.Quotient.eq.mpr (hleib a b) }
  have hdx : Ideal.Quotient.mk (m ^ (k + 1)) (T x - φ' x) = 0 :=
    derivation_apply_eq_zero_of_formallyUnramified d x
  exact Ideal.Quotient.eq_zero_iff_mem.mp hdx

theorem truncatedSeries_sub_mem_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N := by
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have hmulN : ∀ x y : R,
      TaylorExpansion.truncatedSeries φ D β N (x * y)
        - TaylorExpansion.truncatedSeries φ D β N x * TaylorExpansion.truncatedSeries φ D β N y
        ∈ maximalIdeal B ^ N :=
    fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem φ D β N (maximalIdeal B ^ N) hβN x y
  have hbound : ∀ x : P,
      TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x)
        ∈ maximalIdeal B ^ N := fun x => hrep N hN x
  have hbase : ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ 1 := by
    intro x
    rw [pow_one]
    have h1 : TaylorExpansion.truncatedSeries φ D β N x - φ x ∈ Ideal.span ({β} : Set B) :=
      TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN x
    have h2 : Ideal.span ({β} : Set B) ≤ maximalIdeal B := by
      rw [Ideal.span_le]
      simpa using hβ
    have h4 : TaylorExpansion.truncatedSeries φ D β N x - φ' x
        = TaylorExpansion.truncatedSeries φ D β N x - φ x + (φ x - φ' x) := by ring
    rw [h4]
    exact Ideal.add_mem _ (h2 h1) (hcong x)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      ∀ x : R, TaylorExpansion.truncatedSeries φ D β N x - φ' x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
      intro _ hkN
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        exact hbase
      · have hk1' : 1 ≤ k := hk1
        have hkle : maximalIdeal B ^ N ≤ maximalIdeal B ^ (k + 1) :=
          Ideal.pow_le_pow_right hkN
        exact fun x =>
          sub_mem_pow_succ_of_sub_mem_pow P φ' (maximalIdeal B) (TaylorExpansion.truncatedSeries φ D β N) k hk1'
            (fun a b => TaylorExpansion.truncatedSeries_add φ D β N a b)
            (TaylorExpansion.truncatedSeries_one φ D β N hN)
            (fun a b => hkle (hmulN a b))
            (fun p => hkle (hbound p))
            (ih hk1' (by omega)) x
  exact key N hN le_rfl f

theorem sub_mem_span_sup_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N := by
  have h1 : TaylorExpansion.truncatedSeries φ D β N f - φ f ∈ Ideal.span ({β} : Set B) :=
    TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN f
  have h2 : TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N :=
    truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f
  have hEq : φ f - φ' f
      = (TaylorExpansion.truncatedSeries φ D β N f - φ' f) - (TaylorExpansion.truncatedSeries φ D β N f - φ f) := by
    ring
  rw [hEq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)

theorem sub_mem_iInf_span_sup_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ ⨅ N : ℕ, (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N) := by
  refine Submodule.mem_iInf _ |>.2 ?_
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    rw [h0]
    exact Submodule.mem_top
  · exact sub_mem_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f

private theorem mem_of_forall_mem_sup_maximalIdeal_pow {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (x : B)
    (hx : ∀ N : ℕ, x ∈ J ⊔ IsLocalRing.maximalIdeal B ^ N) : x ∈ J := by
  have hmne : IsLocalRing.maximalIdeal B ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hJne : J ≠ ⊤ := by
    intro h
    apply hmne
    rw [eq_top_iff]
    rw [h] at hJ
    exact hJ
  have : Nontrivial (B ⧸ J) := by
    refine ⟨0, 1, fun h => hJne ?_⟩
    rw [Ideal.eq_top_iff_one]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [map_one]
    exact h.symm
  have : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIne : Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) ≠ ⊤ := by
    intro h
    have h1 : (1 : B ⧸ J) ∈ Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 h1
    have h2 : (1 : B) - y ∈ J := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, hy1, map_one, sub_self]
    have h3 : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      have h4 := Submodule.add_mem (IsLocalRing.maximalIdeal B) (hJ h2) hy
      simp at h4
    exact hmne ((Ideal.eq_top_iff_one _).2 h3)
  have hbot : (⨅ i : ℕ,
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) = ⊥ := by
    apply Ideal.iInf_pow_eq_bot_of_isLocalRing
    exact hIne
  have hmem : ∀ N : ℕ, Ideal.Quotient.mk J x ∈
      (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ N := by
    intro N
    obtain ⟨j, hj, y, hy, hxy⟩ := Submodule.mem_sup.1 (hx N)
    have hxe : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
      rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    rw [hxe]
    exact (Ideal.map_pow (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B) N).le
      (Ideal.mem_map_of_mem _ hy)
  have hfin : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, (Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal B)) ^ i) :=
    (Submodule.mem_iInf _).2 hmem
  rw [hbot, Ideal.mem_bot] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.1 hfin

theorem sub_mem_span_singleton_of_isTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) := by
  have h := sub_mem_iInf_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep f
  have hall : ∀ N : ℕ, φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N :=
    (Submodule.mem_iInf _).1 h
  exact mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.span ({β} : Set B))
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 hβ)) (φ f - φ' f) hall

theorem sub_mem_of_isTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (I : Ideal B) (hI : β ∈ I) (f : R) :
    φ f - φ' f ∈ I := by
  have hmem : φ f - φ' f ∈ Ideal.span ({β} : Set B) :=
    sub_mem_span_singleton_of_isTaylorExpansionOn P φ φ' D β hcong hβ hrep f
  have hle : Ideal.span ({β} : Set B) ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI)
  exact hle hmem

theorem map_le_map_of_pow_mul_iterate_deriv_mem (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) (b : R) (J : Ideal R)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (hb : φ b = β)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map φ' J ≤ Ideal.map φ J := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  refine Ideal.mem_comap.mpr ?_
  by_cases htop : Ideal.map φ J = ⊤
  · rw [htop]
    exact Submodule.mem_top
  · refine mem_of_forall_mem_sup_maximalIdeal_pow (Ideal.map φ J)
      (IsLocalRing.le_maximalIdeal htop) (φ' g) ?_
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.mem_top
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h1 : TaylorExpansion.truncatedSeries φ D β n g ∈ Ideal.map φ J := by
        have hmem := truncatedSeries_mem_map φ D b J hstab n g hg
        rwa [hb] at hmem
      have h2 : TaylorExpansion.truncatedSeries φ D β n g - φ' g ∈ maximalIdeal B ^ n :=
        truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep n hn1 g
      have hEq : φ' g = TaylorExpansion.truncatedSeries φ D β n g - (TaylorExpansion.truncatedSeries φ D β n g - φ' g) := by
        ring
      rw [hEq]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

end

end FunctorialResolution.EmbeddedResolution
end
