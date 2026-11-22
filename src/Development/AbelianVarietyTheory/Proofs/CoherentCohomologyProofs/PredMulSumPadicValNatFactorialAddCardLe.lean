module

public import Mathlib

@[expose] public section

namespace GlobalTheory

open Finsupp

section Words

variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]

def opWord (D : Λ → B) (w : List Λ) : B := (w.map D).prod

@[simp] theorem opWord_nil (D : Λ → B) : opWord D [] = 1 := rfl

@[simp] theorem opWord_cons (D : Λ → B) (l : Λ) (w : List Λ) :
    opWord D (l :: w) = D l * opWord D w := by simp [opWord]

@[simp] theorem commEval_X (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) (l : Λ) :
    commEval D hD (MvPolynomial.X l : MvPolynomial Λ R) = D l :=
  opPoly_X D isOrderingRule_toList l

end Words

section General

variable {R A M Λ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]

end General

section Constant

open MvPolynomial

variable {R σ Λ : Type*} [CommRing R]

end Constant

section Series

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R]

noncomputable abbrev germIdeal (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R)

theorem X_mem_germIdeal (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by
  simp [RingHom.mem_ker]

theorem exists_eq_sum_X_mul [Fintype σ] {n : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ d : σ →₀ ℕ, degree d < n + 1 → coeff d g = 0) :
    ∃ h : σ → MvPowerSeries σ R, (∀ i (d : σ →₀ ℕ), degree d < n → coeff d (h i) = 0) ∧
      g = ∑ i, X i * h i := by
  classical
  have hidx : ∀ d : σ →₀ ℕ, d ≠ 0 → ∃ i, d i ≠ 0 := fun d hd => by
    by_contra hc
    push Not at hc
    exact hd (Finsupp.ext hc)
  choose idx hidx using hidx
  let part : σ → MvPowerSeries σ R := fun i d =>
    if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0
  have hpart : ∀ i d, coeff d (part i) =
      if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0 := fun _ _ => rfl
  have hdvd : ∀ i, (X i : MvPowerSeries σ R) ∣ part i := fun i => by
    rw [X_dvd_iff]
    intro d hd
    rw [hpart]
    split_ifs with h₁ h₂
    · exact absurd hd (h₂ ▸ hidx d h₁)
    · rfl
    · rfl
  choose h hh using hdvd
  refine ⟨h, fun i d hd => ?_, ?_⟩
  · have h₁ : coeff (single i 1 + d) (part i) = coeff d (h i) := by
      rw [hh, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h₁, hpart]
    have h₂ : coeff (single i 1 + d) g = 0 := hg _ (by simp; omega)
    simp [h₂]
  · ext d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hh, map_sum, hpart]
    by_cases hd : d = 0
    · subst hd
      simpa using hg 0 (by simp)
    · simp [hd]

theorem germIdeal_eq_span [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  cases nonempty_fintype σ
  refine le_antisymm (fun g hg => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨h, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => by
      obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
      simpa using hg
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact X_mem_germIdeal i

theorem mem_germIdeal_pow_iff [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by
  cases nonempty_fintype σ
  constructor
  · intro hg
    suffices h : (n : ℕ∞) ≤ g.order from fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · refine le_trans ?_ le_order_mul
        push_cast
        refine add_le_add (ih ha) ?_
        exact_mod_cast nat_le_order (n := 1) fun d hd => by
          obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
          simpa using hb
      · exact (le_min ha hb).trans min_order_le_add
  · induction n generalizing g with
    | zero => simp
    | succ n ih =>
      intro hg
      obtain ⟨h, hh, rfl⟩ := exists_eq_sum_X_mul hg
      rw [pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_germIdeal i) (ih (hh i))

theorem mem_germIdeal_pow_iff_le_order [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by
  rw [mem_germIdeal_pow_iff]
  exact ⟨nat_le_order, fun h d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩

variable [Finite σ]

end Series

section Symbol

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R] [Finite σ] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M]

variable [IsScalarTower R (MvPowerSeries σ R) M]

end Symbol

section Example

open MvPowerSeries

end Example

section Legendre

variable {l : ℕ} [hl : Fact l.Prime]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

end Legendre

end GlobalTheory
