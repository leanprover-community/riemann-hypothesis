import Mathlib
import Formalism.PeriodIntegrals.CapelliEig
open Matrix MeasureTheory
noncomputable section
namespace GlobalTheory.Survey.MatrixExponentialEntries
open PI.UpqRep

abbrev M₁ := Matrix (Fin 1) (Fin 1) ℂ

def chi (m : ℤ) (g : M₁) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

theorem norm_entry {ε : Fin 1 → Bool} {g : M₁} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by
  have h := congrFun (congrFun hg 0) 0
  simp only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  have h2 := congrArg norm h
  have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  simp only [norm_mul, norm_star, h3] at h2
  nlinarith [norm_nonneg (g 0 0)]

theorem wt_eq {ε : Fin 1 → Bool} (m : ℤ) (μ : Fin 1 → ℝ) (v : ℂ) (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) (chi m) μ v) : μ = fun _ => (m : ℝ) := by
  have key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    have hK : Matrix.diagonal (fun a : Fin 1 => Complex.exp (((fun _ => t) a : ℝ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.mem_unitaryGroup_iff]
        ext i j
        obtain rfl : i = 0 := Subsingleton.elim _ _
        obtain rfl : j = 0 := Subsingleton.elim _ _
        simp [Matrix.mul_apply, Matrix.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
      · simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]
    have h1 := h (fun _ => t) hK
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




abbrev W₂ := EuclideanSpace ℂ (Fin 2)

end GlobalTheory.Survey.MatrixExponentialEntries
