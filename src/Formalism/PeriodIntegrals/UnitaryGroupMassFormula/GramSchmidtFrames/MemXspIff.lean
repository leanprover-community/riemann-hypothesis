import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def SatOm : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW k r z z' (n * y * n') = omW k r z z' y

def SatOm' : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW' k r z z' (n * y * n') = omW' k r z z' y

section lemmas

variable {k r : ℕ}

lemma mem_Xsp_iff (v : Fin (2 * r + k + 1) → ℂ) : v ∈ Xsp k r ↔ ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h
      have ha := a.isLt
      rw [h] at hi
      simp only [eI] at hi
      omega
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul c x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ a : Fin r, v (eI k r a) • bvec (eI k r a) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i.val < r
      · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
        · have he : i = eI k r ⟨i.val, hi⟩ := by ext; rfl
          rw [if_pos he, ← he]
        · intro b _ hb
          rw [if_neg]
          intro h
          apply hb
          ext
          show b.val = i.val
          have h2 := congrArg Fin.val h
          simp only [eI] at h2
          omega
        · simp
      · rw [hv i (by omega)]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [if_neg]
        intro h
        have hb := b.isLt
        rw [h] at hi
        simp only [eI] at hi
        omega
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)


lemma N_wb {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ Xsp k r := by
  rw [mem_Xsp_iff]
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [sub_eq_zero, Finset.sum_eq_single i]
  · by_cases hmid : i.val ≤ r + k
    · rw [hn.2.2 i i hi hmid hi, if_pos rfl, one_mul]
    · rw [hu i (Or.inr (by omega)), mul_zero]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [hn.2.2 i j hj.1 hj.2 hi, if_neg (Ne.symm hji), zero_mul]
    · rw [hu j (by omega), mul_zero]
  · simp

end lemmas


end PI.UnitaryGroupMassFormula.GsFr
