module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Mathlib.Tactic.Lemma
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section aux

variable {k r : ℕ}

lemma uw_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {α : B.Mat k r} (hα : α ∈ UWset k r z)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (α *ᵥ u) := by
  unfold UWset at hα
  simp only [Set.mem_setOf_eq] at hα
  obtain ⟨hU, hfix, -⟩ := hα
  unfold UH at hU
  simp only [Set.mem_setOf_eq] at hU
  have key : ∀ x w : Fin (2 * r + k + 1) → ℂ,
      star (α *ᵥ w) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ x)) = star w ⬝ᵥ (Hpk k r *ᵥ x) := by
    intro x w
    rw [Matrix.star_mulVec, ← dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, hU]
  have hstar : ∀ (w : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)),
      star w ⬝ᵥ Pi.single j 1 = star (w j) := by
    intro w j
    rw [dotProduct_single, mul_one]
    rfl
  have hH : ∀ a : Fin r, Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) ∧
      Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
    intro a
    have ha := a.isLt
    constructor
    all_goals
      funext i
      have hi := i.isLt
      unfold Hpk bvec eI esI
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff] at *; omega)
  have gen : ∀ (i : Fin (2 * r + k + 1)) (b : Fin (2 * r + k + 1) → ℂ), α *ᵥ b = b →
      Hpk k r *ᵥ b = Pi.single i 1 → star ((α *ᵥ u) i) = star (u i) := by
    intro i b hb hHb
    calc star ((α *ᵥ u) i) = star (α *ᵥ u) ⬝ᵥ Pi.single i 1 := (hstar _ _).symm
      _ = star (α *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (α *ᵥ b)) := by rw [hb, hHb]
      _ = star u ⬝ᵥ (Hpk k r *ᵥ b) := key _ _
      _ = star (u i) := by rw [hHb, hstar]
  intro i hi
  refine star_eq_zero.mp ?_
  rcases hi with hi | hi
  · have he : bvec (eI k r ⟨i, hi⟩) = Pi.single i 1 := by
      unfold bvec eI
      rfl
    rw [gen i (bvec (esI k r ⟨i, hi⟩)) (hfix _).2 (by rw [(hH _).1, he]), hu i (Or.inl hi),
      star_zero]
  · have hi2 := i.isLt
    have h' : 2 * r + k - (i : ℕ) < r := by omega
    have he : bvec (esI k r ⟨2 * r + k - i, h'⟩) = Pi.single i 1 := by
      unfold bvec esI
      dsimp only
      congr 1
      ext
      simp only
      omega
    rw [gen i (bvec (eI k r ⟨2 * r + k - i, h'⟩)) (hfix _).1 (by rw [(hH _).2, he]),
      hu i (Or.inr hi), star_zero]

lemma det_ne_of_G {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hG : 0 < Gf k r z z' y) : (Zhat k r z z' y).det ≠ 0 := by
  have hD : Dmin k r z z' y (Fin.last (r + 1)) ≠ 0 := by
    intro h
    unfold Gf at hG
    rw [h, map_zero] at hG
    have := mul_nonneg (mul_nonneg hz.2.le hz'.2.le) (Complex.normSq_nonneg (Dmin k r z z' y ⟨r, by omega⟩))
    linarith
  unfold Dmin at hD
  have hid : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) : Fin (r + 1) → Fin (r + 1)) = id :=
    funext fun i => Fin.ext rfl
  rwa [hid, Matrix.submatrix_id_id] at hD

end aux

end PI.UnitaryGroupMassFormula.GsFr
