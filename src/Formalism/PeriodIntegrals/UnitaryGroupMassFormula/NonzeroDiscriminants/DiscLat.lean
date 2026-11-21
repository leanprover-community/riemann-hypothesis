import Mathlib
import Formalism.PeriodIntegrals.DiscrNe

open ModularForm EisensteinSeries UpperHalfPlane

noncomputable section

namespace DiscrNeWork

lemma lin_inj (τ : ℍ) {m n m' n' : ℤ} (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') :
    m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  first
    | simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at him
    | simp at him
  have key : ((m : ℝ) - m') * (τ : ℂ).im = 0 := by
    first
      | linear_combination him
      | linarith
  have hpos : 0 < (τ : ℂ).im := τ.im_pos
  have hsub : (m : ℝ) - m' = 0 := (mul_eq_zero.mp key).resolve_right hpos.ne'
  have hm : m = m' := by exact_mod_cast sub_eq_zero.mp hsub
  subst hm
  refine ⟨rfl, ?_⟩
  have hn : (n : ℂ) = n' := add_left_cancel h
  exact_mod_cast hn

lemma lin_ne (τ : ℍ) (v : Fin 2 → ℤ) (hv : v ≠ 0) : ((v 0 : ℂ) * τ + v 1) ≠ 0 := by
  intro h0
  apply hv
  have h' : ((v 0 : ℤ) : ℂ) * τ + ((v 1 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ) := by
    first
      | (rw [h0]; simp)
      | simpa using h0
  obtain ⟨h1, h2⟩ := lin_inj τ h'
  funext i
  fin_cases i
  · exact h1
  · exact h2

def nz : Set (Fin 2 → ℤ) := {v | v ≠ 0}

def toLat (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (v : nz) :
    {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} :=
  ⟨a * ((v.1 0 : ℂ) * τ + v.1 1), by
    refine ⟨?_, mul_ne_zero ha (lin_ne τ v.1 v.2)⟩
    rw [PI.lat2, AddSubgroup.mem_closure_pair]
    exact ⟨v.1 1, v.1 0, by simp only [zsmul_eq_mul]; ring⟩⟩



end DiscrNeWork

end
