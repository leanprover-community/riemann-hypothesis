import Mathlib
import Formalism.PeriodIntegrals.UpqRep

noncomputable section

open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.DiscreteSeriesTest

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - a := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e1 : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have e2 : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  rw [e1, Fin.card_Ioi] at h1
  rw [e2, Fin.card_Iio] at h2
  have ha := a.isLt
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - a := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  rw [h3] at h1'
  push_cast at h1' h2'
  simp only [rhoN, rhoC, ne_eq]
  linarith

theorem lowK_add {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (((n : ℝ) - 1) / 2 - a) := by
  rw [← rhoN_add_rhoC ε a]
  simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring


theorem torus_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

theorem wt_int {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  have h2 := h (Pi.single a (2 * Real.pi)) (torus_mem ε _)
  have e : (Matrix.diagonal fun b => Complex.exp (((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  rw [e, h1] at h2
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    apply smul_left_injective ℂ hv
    simpa using h2.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨m, ?_⟩
  have h4 := congrArg Complex.im hm
  simp at h4
  exact h4

theorem isHCParam_of_isDS {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hl : StrictAnti lam) (h : IsDS ε lam σ) :
    IsHCParam lam := by
  refine ⟨hl, fun a => ?_⟩
  obtain ⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩ := h
  obtain ⟨m, hm⟩ := wt_int h1 hv0 hv a
  have h2 := lowK_add ε lam a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, rhoC] at h2
  refine ⟨m + (univ.filter fun b => a < b ∧ ε b = ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card
    - (n - 1) + a, ?_⟩
  push_cast
  linarith

theorem norm_entry {ε : Fin 1 → Bool} {g : Matrix (Fin 1) (Fin 1) ℂ} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by
  have h := congrFun (congrFun hg 0) 0
  simp only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  have h2 := congrArg norm h
  have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  simp only [norm_mul, norm_star, h3] at h2
  nlinarith [norm_nonneg (g 0 0)]

def chi (m : ℤ) (g : Matrix (Fin 1) (Fin 1) ℂ) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

theorem wt_eq {ε : Fin 1 → Bool} (m : ℤ) (μ : Fin 1 → ℝ) (v : ℂ) (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) (chi m) μ v) : μ = fun _ => (m : ℝ) := by
  have key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    have h1 := h (fun _ => t) (torus_mem ε _)
    simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hv h1
    rw [← Complex.exp_int_mul] at h2
    have : (((μ 0 - m) * t : ℝ) : ℂ) * Complex.I = ((μ 0 * t : ℝ) : ℂ) * Complex.I - m * (t * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_sub, ← h2, div_self (Complex.exp_ne_zero _)]
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  by_contra hne
  have hne' : μ 0 - m ≠ 0 := sub_ne_zero.2 hne
  have := key (Real.pi / (μ 0 - m))
  rw [mul_div_cancel₀ _ hne', Complex.exp_pi_mul_I] at this
  norm_num at this





end GlobalTheory.DiscreteSeriesTest
