import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.StThmAFull
import ReciprocityTheory.DualLattices.VDetEqOneOfIntegral

section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def IsotypicAveragingStatement : Prop :=
  ∀ (S : Type) [CommRing S] (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) S)
    (E : Matrix (Ix g) (Ix g) S) (cp : S)
    (εT : Fin m → Matrix (Ix g) (Ix g) S) (εL : Fin m → Matrix (Fin g) (Fin g) S)
    (π : Equiv.Perm (Fin m)),
    (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    Btᵀ * Ht - Htᵀ * Bt = cp • E →
    let Bt' := ∑ i, εL i * Bt * εT i
    (Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E) ∧ (∀ i, Bt' * εT i = εL i * Bt') ∧
    (Matrix.fromRows Ht Bt').det ^ 2 = cp ^ (2 * g) * E.det

end ReciprocityTheory.PGsh.Up
end
end

section
noncomputable section

open Matrix TensorProduct

namespace ReciprocityTheory.PGsh

section Mat

variable {D : Type} [CommRing D] {g : ℕ}

lemma stdJ_mul_self : stdJ D g * stdJ D g = -1 := by
  ext (i | i) (j | j) <;> simp [stdJ, Matrix.fromBlocks_multiply, Matrix.one_apply]

lemma det_stdJ_sq : (stdJ D g).det ^ 2 = 1 := by
  rw [sq, ← Matrix.det_mul, stdJ_mul_self, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_sum,
    Fintype.card_fin, ← two_mul, pow_mul]
  simp

lemma isUnit_det_stdJ : IsUnit (stdJ D g).det := by
  exact isUnit_iff_exists_inv.2 ⟨(stdJ D g).det, by rw [← sq, det_stdJ_sq]⟩

lemma det_sq_eq (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by
  have h := congrArg Matrix.det hJ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_sum, Fintype.card_fin,
    ← two_mul] at h
  have hJ2 := det_stdJ_sq (D := D) (g := g)
  calc Φ.det ^ 2 = Φ.det ^ 2 * ((stdJ D g).det ^ 2) := by rw [hJ2, mul_one]
    _ = (Φ.det * (stdJ D g).det * Φ.det) * (stdJ D g).det := by ring
    _ = c ^ (2 * g) * (E.det * (stdJ D g).det) := by rw [h]; ring

end Mat

section Span

variable {R₀ : Type} [CommRing R₀]

end Span

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Val

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma stdJ_form' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib,
    sub_eq_add_neg, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

private lemma stdJ_eq (D : Type) [CommRing D] (g : ℕ) :
    stdJ D g = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
  rw [stdJ]
  simp [Matrix.fromBlocks_multiply]

private lemma det_stdJ (D : Type) [CommRing D] (g : ℕ) : (stdJ D g).det = 1 := by
  rw [stdJ_eq, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

theorem u1 : IsotypicAveragingStatement := by
  intro S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH
  intro Bt'
  have hBt' : Bt' = ∑ i, εL i * Bt * εT i := rfl
  have hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i) := by
    intro i
    have h := hHt (π i)
    rw [hπ] at h
    exact h.symm
  have hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ := by
    intro i
    have h := congrArg Matrix.transpose (hLt i)
    simpa [Matrix.transpose_mul] using h
  have part2 : ∀ i, Bt' * εT i = εL i * Bt' := by
    intro i
    have l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      rw [Matrix.mul_assoc (εL j * Bt), hT j i]
      split_ifs with h
      · subst h; rfl
      · simp
    have r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]
      · rw [if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h),
          Matrix.zero_mul, Matrix.zero_mul]
    rw [hBt', Matrix.sum_mul, Matrix.mul_sum]
    simp only [l, r]
  have hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) := by
    rw [hBt', Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [hLt i]
  have hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i) := by
    rw [hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [hHtL (π i), hπ]
  have part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    have h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) =
        cp • (E * εT (π i)) := by
      intro i
      rw [Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul,
        ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT,
        if_pos rfl]
    simp only [h]
    rw [← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]
  have hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E := by
    rw [← part1]
    ext i j
    rw [stdJ_form']
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  refine ⟨part1, part2, ?_⟩
  rw [det_sq_eq E _ cp hJ, det_stdJ, mul_one]

end ReciprocityTheory.PGsh.Up
end
end
