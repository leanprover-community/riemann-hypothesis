import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntegralNormSqCoef

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have key : ∀ (c : ℕ) (hc : c < 2 * r + k + 1) (a : ℂ),
      ∑ j : Fin (2 * r + k + 1), (if j.val = c then a else 0) * v j = a * v ⟨c, hc⟩ := by
    intro c hc a
    rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp
    · intro b _ hb
      have hbc : b.val ≠ c := fun h => hb (Fin.ext h)
      simp [hbc]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [hpk_out k r h]
    rw [key _ (by omega), one_mul]
  · rw [if_neg h]
    simp only [hpk_mid k r h]
    rw [key i.val hi]
    split_ifs <;> simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem one_mem_UH (k r : ℕ) : (1 : Mat k r) ∈ UH (Hpk k r) := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp


theorem coef_mul (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ)
    (y g : Mat k r) (hy : y ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    ⟪w, σ (y * g) w⟫_ℂ = ⟪σ y⁻¹ w, σ g w⟫_ℂ := by
  have hyi := inv_mem_UH k r y hy
  have hmul := hσ.1.2
  have h1 : σ y (σ y⁻¹ w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul y hy y⁻¹ hyi, mul_inv_UH k r hy, hσ.1.1]
    rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(σ y).toLinearMap, hσ.2.1 y hy⟩
  have hL := L.inner_map_map (σ y⁻¹ w) (σ g w)
  rw [hmul y hy g hg, ContinuousLinearMap.comp_apply]
  have e : ⟪w, σ y (σ g w)⟫_ℂ = ⟪σ y (σ y⁻¹ w), σ y (σ g w)⟫_ℂ := by rw [h1]
  rw [e]
  exact hL



end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
