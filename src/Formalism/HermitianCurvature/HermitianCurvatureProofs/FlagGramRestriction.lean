import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma col_V_mul (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (Φ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (gnB k r z z' γ * Φ) a j) = ∑ i, Φ i j • gramVec k r z z' γ i := by
  funext a; simp [gnB, Matrix.mul_apply, Finset.sum_apply, mul_comm]

lemma mat_ext_col {n : ℕ} {ι : Type*} (A B : Matrix (Fin n) ι ℂ) (h : ∀ j, (fun a => A a j) = fun a => B a j) :
    A = B := by
  ext a j; exact congrFun (h j) a

def PhiH (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ h : B.Mat k r) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (C2.uMap k r z h) 0 0 (C2.uMap k r z' (γ⁻¹ * h * γ))


lemma mulV {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hγ : IsUnit γ.det)
    {h : B.Mat k r} (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') :
    h * gnB k r z z' γ = gnB k r z z' γ * PhiH k r z z' γ h := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  apply mat_ext_col
  intro j
  rw [col_mul, col_V_mul, Fintype.sum_sum_type]
  cases j with
  | inl b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact hU.1 b
  | inr b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    show h *ᵥ (γ *ᵥ fvec k r z' b) = ∑ c, C2.uMap k r z' (γ⁻¹ * h * γ) c b • (γ *ᵥ fvec k r z' c)
    have e : h * γ = γ * (γ⁻¹ * h * γ) := by
      simp only [Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hU'.1 b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]




lemma flag_mem (z : Fin (2 * r + k + 1) → ℂ) (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hu : u ∈ C2.UTset (r + 1))
    (b : Fin (r + 1)) : (∑ c, u c b • fvec k r z c) - fvec k r z b ∈ C2.flagSpan k r z b := by
  have e : (∑ c, u c b • fvec k r z c) - fvec k r z b =
      ∑ c, (u c b - if c = b then 1 else 0) • fvec k r z c := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e]
  apply Submodule.sum_mem
  intro c _
  by_cases hcb : c < b
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨c, hcb⟩, rfl⟩
  · have h0 : u c b - (if c = b then 1 else 0) = 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hcb) with h | h
      · rw [hu.1 c b h, if_neg (ne_of_gt h), sub_self]
      · subst h; rw [hu.2, if_pos rfl, sub_self]
    rw [h0, zero_smul]; exact Submodule.zero_mem _

lemma cancel_left {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : A * X = A * Y) : X = Y := by
  calc X = A⁻¹ * (A * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = A⁻¹ * (A * Y) := by rw [h]
    _ = Y := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

lemma cancel_right {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : X * A = Y * A) : X = Y := by
  calc X = X * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
    _ = Y * A * A⁻¹ := by rw [h]
    _ = Y := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]



end FlagGramRestriction

end Formalism.FourierDecayAlt.P
