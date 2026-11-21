import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.WordMonicExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7

private theorem lagsum_lemma {F : Type} [Field F] {d : ℕ} (v : Fin (d + 1) → F)
    (hv : Function.Injective v) (P : Polynomial F) (hP : P.natDegree ≤ d) :
    ∑ j, (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) * P.eval (v j) = P.coeff d := by
  have hdeg : P.degree < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hP)
  have hI := Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv.injOn hdeg
  conv_rhs => rw [hI]
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hb : Lagrange.basis Finset.univ v j =
      Polynomial.C (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) *
        Lagrange.nodal (Finset.univ.erase j) v := by
    unfold Lagrange.basis Lagrange.basisDivisor Lagrange.nodal
    rw [Finset.prod_mul_distrib, map_prod]
  have hn : (Lagrange.nodal (Finset.univ.erase j) v).natDegree = d := by
    rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hm := (Lagrange.nodal_monic (s := Finset.univ.erase j) (v := v)).coeff_natDegree
  rw [hn] at hm
  rw [Polynomial.coeff_C_mul, hb, Polynomial.coeff_C_mul, hm]
  ring

theorem moment (d : ℕ) (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ) (hk : k ≤ d) :
    ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have h := lagsum_lemma y hy (Polynomial.X ^ k) (by rw [Polynomial.natDegree_X_pow]; exact hk)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow] at h
  simp only [lagCo]
  rw [h]
  exact if_congr eq_comm rfl rfl



section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem evR_smul (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by
  unfold evR
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ha), Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← map_pow, ← Algebra.commutes, mul_smul, algebraMap_smul]

end

theorem isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  unfold IsTopCoeff at h h' ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  obtain ⟨P', hP', hPc', hW'⟩ := h'
  exact ⟨P - P', (Polynomial.natDegree_sub_le _ _).trans (max_le hP hP'),
    by rw [Polynomial.coeff_sub, hPc, hPc'], fun Y => by simp only [Polynomial.eval_sub, hW, hW']⟩

theorem isTop_const_mul {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  unfold IsTopCoeff at h ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  exact ⟨Polynomial.C k * P, (Polynomial.natDegree_C_mul_le _ _).trans hP,
    by rw [Polynomial.coeff_C_mul, hPc], fun Y => by simp only [Polynomial.eval_C_mul, hW]⟩

theorem natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [(Polynomial.monic_X_pow i).natDegree_mul ((Polynomial.monic_X_add_C h).pow j),
    Polynomial.natDegree_X_pow, (Polynomial.monic_X_add_C h).natDegree_pow, Polynomial.natDegree_X_add_C,
    mul_one]

theorem coeff_mono (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  by_cases hij : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    have hm := ((Polynomial.monic_X_pow i).mul ((Polynomial.monic_X_add_C h).pow j)).coeff_natDegree
    rw [natDegree_mono] at hm
    exact hm
  · rw [if_neg hij]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem pairTop (Ξ : Sesq M) (P₁ P₂ : R[X]) (a b : ℕ) (h : ℝ) (X X' : M)
    (ha : P₁.natDegree ≤ a) (hb : P₂.natDegree ≤ b) :
    IsTopCoeff (fun Y => Ξ (evR P₁ Y • X) (evR P₂ (Y + h) • X')) (a + b)
      (Ξ (P₁.coeff a • X) (P₂.coeff b • X')) := by
  unfold IsTopCoeff
  refine ⟨∑ i ∈ range (a + 1), ∑ k ∈ range (b + 1),
    Polynomial.C (Ξ (P₁.coeff i • X) (P₂.coeff k • X')) *
      (Polynomial.X ^ i * (Polynomial.X + Polynomial.C (h : ℂ)) ^ k), ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    rw [Finset.mem_range] at hi hk
    omega
  · rw [Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_range.mpr (Nat.lt_succ_self a)) ?_]
    · rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.mpr (Nat.lt_succ_self b)) ?_]
      · rw [coeff_mono _ _ _ _ _ le_rfl le_rfl, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro k hk hkb
        rw [coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          if_neg (fun hh => hkb hh.2), mul_zero]
    · intro i hi hia
      apply Finset.sum_eq_zero
      intro k hk
      rw [coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), if_neg (fun hh => hia hh.1), mul_zero]
  · intro Y
    beta_reduce
    rw [evR_smul P₁ a ha Y X, evR_smul P₂ b hb (Y + h) X']
    simp only [map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, map_pow, map_add, Complex.conj_ofReal,
      Complex.ofReal_add, Finset.mul_sum, Finset.sum_mul]
    first
      | (refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)

noncomputable def letterVal (Ξ : Sesq M) (D : Dat R) (y : ℝ) (x x' : M) : ℂ :=
  Ξ ((evR D.B y + algebraMap ℂ R D.s * evR D.A y) • x) (evR D.Av (y + 1) • x') -
    Ξ (evR D.A y • x) (evR D.Bv (y + 1) • x')








end

end Formalism.FourierDecayAlt.P.WordMonicExtraction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction





end Formalism.FourierDecayAlt.P
