import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit

section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

theorem sel_factor (ϖ : R) (hϖ0 : ϖ ≠ 0)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι κ : Type} (h : Matrix ι κ R) (hh : h ≠ 0) :
    ∃ (m : ℕ) (h₁ : Matrix ι κ R) (i : ι) (j : κ), h = ϖ ^ m • h₁ ∧ IsUnit (h₁ i j) := by
  classical
  have hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u := by
    by_contra hne
    apply hh
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    obtain ⟨n, u, hu, he⟩ := hval _ hij
    exact hne ⟨n, i, j, hij, u, hu, he⟩
  obtain ⟨i₀, j₀, _, u₀, hu₀, he₀⟩ := Nat.find_spec hex
  have hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z := by
    intro i j
    by_cases hij : h i j = 0
    · exact ⟨0, by rw [hij, mul_zero]⟩
    · obtain ⟨n, u, hu, he⟩ := hval _ hij
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩
      refine ⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩
      rw [he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  choose h₁ hh₁ using hdiv
  refine ⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact hh₁ i j
  · have e : h₁ i₀ j₀ = u₀ :=
      mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)
    simp only [Matrix.of_apply, e]
    exact hu₀

theorem sel_star_smul (σ : R ≃+* R) (ϖ : R) (hσϖ : σ ϖ = ϖ) (m : ℕ) {ι κ : Type}
    (h : Matrix ι κ R) : ((ϖ ^ m • h).map σ)ᵀ = ϖ ^ m • (h.map σ)ᵀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hσϖ]

theorem sel_smul_cancel {ι κ : Type} {c : R} (hc : c ≠ 0) {X Y : Matrix ι κ R}
    (h : c • X = c • Y) : X = Y := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_left_cancel₀ hc h'

theorem sel_le (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by
  have hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A' := by
    rw [← hrel, sel_star_smul σ ϖ hσϖ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
  have hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0 := fun t => pow_ne_zero _ hϖ0
  by_cases hmk : m ≤ k
  · refine ⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩
    rw [hB, smul_smul, ← pow_add]
    congr 2
    omega
  · exfalso
    push_neg at hmk
    have h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A' := by
      rw [smul_smul, ← pow_add, ← hB]
      congr 2
      omega
    have h3 := sel_smul_cancel (hp0 (2 * k)) h2
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_smul] at h4
    rw [← h4] at hA'
    have h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι) := isUnit_of_mul_isUnit_left hA'
    rw [← pow_mul] at h5
    have hpos : 2 * (m - k) * Fintype.card ι ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)
    exact hϖ ((isUnit_pow_iff hpos).mp h5)

theorem sel_unit_of_rel (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = A') : IsUnit h₁.det := by
  have e := congrArg Matrix.det hrel
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hA'
  exact isUnit_of_mul_isUnit_right hA'

theorem sel_comm {ι : Type} [Fintype ι] [DecidableEq ι] {c : R} (hc : c ≠ 0)
    (g h : Matrix ι ι R) (hgh : g * h = c • 1) : h * g = c • 1 := by
  have hdet : g.det * h.det = c ^ Fintype.card ι := by
    rw [← Matrix.det_mul, hgh, Matrix.det_smul, Matrix.det_one, mul_one]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have key : (h * g - c • 1) * h = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hgh, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have key2 : h.det • (h * g - c • 1) = 0 := by
    have e := congrArg (· * h.adjugate) key
    simp only [Matrix.zero_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e
    exact e
  have e0 : h * g - c • 1 = 0 := by
    ext i j
    have e := congrFun (congrFun key2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e ⊢
    exact (mul_eq_zero.mp e).resolve_left hh0
  exact sub_eq_zero.mp e0

theorem sel_inv (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) {c : R} (hc : c ≠ 0)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = c • A') :
    (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 ∧ h₁ * (A'⁻¹ * (h₁.map σ)ᵀ * A) = c • 1 := by
  have h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hA']
  exact ⟨h1, sel_comm hc _ _ h1⟩

theorem sel_dual (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : IsUnit A.det) (x : ι → R) (i : ι) (hx : IsUnit (x i)) :
    ∃ y : ι → R, (fun l => σ (x l)) ⬝ᵥ (A *ᵥ y) = 1 := by
  obtain ⟨u, hu⟩ := hx.map σ
  refine ⟨A⁻¹ *ᵥ Pi.single i (↑u⁻¹ : R), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec, dotProduct_single]
  simp [← hu]

theorem sel_form (σ : R ≃+* R) {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (M : Matrix ι κ R) (v w : κ → R) :
    (fun l => σ ((M *ᵥ v) l)) ⬝ᵥ (A *ᵥ (M *ᵥ w)) =
      (fun l => σ (v l)) ⬝ᵥ (((M.map σ)ᵀ * A * M) *ᵥ w) := by
  have e : (fun l => σ ((M *ᵥ v) l)) = (M.map σ) *ᵥ (fun l => σ (v l)) := by
    funext l
    exact RingHom.map_mulVec (σ : R →+* R) M v l
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end PI.SqPair.LCP
end
end

section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

theorem sel_main (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h : Matrix ι ι R) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (k : ℕ)
    (hrel : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A') :
    ∃ (m : ℕ) (h₁ : Matrix ι ι R), h = ϖ ^ m • h₁ ∧ m ≤ k ∧
      (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' ∧
      ((m = k ∧ IsUnit h₁.det) ∨
       (m < k ∧ ∃ (g₁ : Matrix ι ι R) (j : ι) (y : ι → R),
          g₁ * h₁ = ϖ ^ (2 * (k - m)) • 1 ∧ h₁ * g₁ = ϖ ^ (2 * (k - m)) • 1 ∧
          (∃ i, IsUnit ((h₁ *ᵥ Pi.single j 1) i)) ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ y) = 1 ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ (h₁ *ᵥ Pi.single j 1)) =
            ϖ ^ (2 * (k - m)) * A' j j ∧
          ϖ ^ (2 * (k - m)) • y = h₁ *ᵥ (g₁ *ᵥ y))) := by
  have hc : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n hϖ0
  have hh : h ≠ 0 := by
    rintro rfl
    have h0 : ϖ ^ (2 * k) • A' = 0 := by rw [← hrel]; simp
    rcases smul_eq_zero.1 h0 with h2 | h2
    · exact hc _ h2
    · rw [h2, Matrix.det_zero] at hA'
      exact not_isUnit_zero hA'
  obtain ⟨m, h₁, i, j, rfl, hu⟩ := sel_factor ϖ hϖ0 hval h hh
  obtain ⟨hmk, hrel₁⟩ := sel_le σ ϖ hϖ0 hϖ hσϖ A A' h₁ hA' m k hrel
  refine ⟨m, h₁, rfl, hmk, hrel₁, ?_⟩
  rcases Nat.lt_or_ge m k with hlt | hge
  · right
    refine ⟨hlt, ?_⟩
    obtain ⟨hg1, hg2⟩ := sel_inv σ A A' h₁ hA' (hc _) hrel₁
    have hxi : IsUnit ((h₁ *ᵥ Pi.single j 1) i) := by simpa [Matrix.mulVec_single] using hu
    obtain ⟨y, hy⟩ := sel_dual σ A hA (h₁ *ᵥ Pi.single j 1) i hxi
    refine ⟨A'⁻¹ * (h₁.map σ)ᵀ * A, j, y, hg1, hg2, ⟨i, hxi⟩, hy, ?_, ?_⟩
    · rw [sel_form σ A h₁ (Pi.single j 1) (Pi.single j 1), hrel₁]
      have hs : (fun l : ι => σ ((Pi.single j (1 : R) : ι → R) l)) = (Pi.single j 1 : ι → R) := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp
        · simp [Pi.single_apply, hl]
      rw [hs]
      simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]
    · rw [Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]
  · left
    have hm : m = k := le_antisymm hmk hge
    subst hm
    refine ⟨rfl, ?_⟩
    rw [Nat.sub_self, mul_zero, pow_zero, one_smul] at hrel₁
    exact sel_unit_of_rel σ A A' h₁ hA' hrel₁

end PI.SqPair.LCP
end
end

section
noncomputable section
open Matrix

namespace PI.SqPair.LCP

theorem pair_selection : Select := by
  intro R _ _ R₀ ϖ hI ι _ _ A A' h k hP hNB
  have := hI.dom
  obtain ⟨⟨_, hA⟩, ⟨_, hA'⟩, hrel⟩ := hP
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hNB ⟨1, by simp, by ext i; exact (IsEmpty.false i).elim⟩
  let σ : R ≃+* R := starRingAut
  have hct : ∀ M : Matrix ι ι R, (M.map σ)ᵀ = Mᴴ := by
    intro M; ext i j; simp [σ, Matrix.conjTranspose_apply]
  have hs : ∀ x : ι → R, star x = fun l => σ (x l) := by
    intro x; ext l; simp [σ]
  have hσϖ : σ ϖ = ϖ := by simpa [σ] using (hI.fix ϖ).mp hI.pi_mem
  have hrel' : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A' := by rw [hct]; exact hrel
  obtain ⟨m, h₁, rfl, hle, _, hcase⟩ :=
    sel_main σ ϖ hI.pi_ne hI.pi_nonunit hσϖ hI.val A A' h hA hA' k hrel'
  rcases hcase with ⟨hmk, hu⟩ | ⟨hlt, g₁, j, y, _, _, _, hxy, hxx, hy⟩
  · exact absurd ⟨h₁, hu, by rw [hmk]⟩ hNB
  · refine ⟨k - m, h₁ *ᵥ Pi.single j 1, y, by omega, by omega, ?_, ⟨A' j j, ?_⟩,
      ⟨Pi.single j 1, ?_⟩, ⟨g₁ *ᵥ y, ?_⟩⟩
    · unfold hf; rw [hs]; exact hxy
    · unfold hf; rw [hs]; exact hxx
    · rw [Matrix.smul_mulVec, show k - (k - m) = m by omega]
    · rw [Matrix.smul_mulVec, ← hy, smul_smul, ← pow_add]
      congr 2
      omega

end PI.SqPair.LCP
end
end
