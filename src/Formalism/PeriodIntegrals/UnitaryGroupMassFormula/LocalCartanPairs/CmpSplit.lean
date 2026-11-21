import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit

section
noncomputable section
open Matrix

namespace PI.SqPair.LocCartanPairW

variable {R : Type*} [CommRing R] (σ : R ≃+* R)






end PI.SqPair.LocCartanPairW
end
end

section
noncomputable section
open Matrix

namespace PI.SqPair.LocCartanPairW

variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem cmp_map_mulVec {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (v : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) = h.map σ *ᵥ (fun i => σ (v i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem cmp_gram_pull {ι : Type*} [Fintype ι] (A h : Matrix ι ι R) (v w : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) ⬝ᵥ (A *ᵥ (h *ᵥ w)) =
      (fun i => σ (v i)) ⬝ᵥ (((h.map σ)ᵀ * A * h) *ᵥ w) := by
  rw [cmp_map_mulVec σ h v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec _ (h.map σ)ᵀ, Matrix.vecMul_transpose]

theorem cmp_gram_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι R) (a b : R) (v w : ι → R) :
    (fun i => σ ((a • v) i)) ⬝ᵥ (A *ᵥ (b • w)) = σ a * b * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
  have h1 : (fun i => σ ((a • v) i)) = σ a • fun i => σ (v i) := by
    funext i; simp [map_mul]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (fun i => σ a * σ (v i)) ⬝ᵥ (A *ᵥ w) = σ a * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  have h3 : (σ a • fun i => σ (v i)) = fun i => σ a * σ (v i) := by
    funext i; simp
  rw [h3, h2]; ring

private lemma smulMulVec_lemma {ι : Type*} [Fintype ι] (a : R) (M : Matrix ι ι R) (v : ι → R) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem cmp_gram_pre [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R)
    (hs : s ≠ 0) (hh : (h.map σ)ᵀ * A * h = s • A') (v w x y : ι → R) (c d t : R)
    (hv : h *ᵥ v = c • x) (hw : h *ᵥ w = d • y)
    (hxy : (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) = s * t) :
    (fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w) = t := by
  have key : s • ((fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w)) =
      (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) := by
    rw [← dotProduct_smul, ← smulMulVec_lemma, ← hh, ← cmp_gram_pull σ A h v w, hv, hw,
      cmp_gram_smul σ A c d x y]
    ring
  rw [hxy, smul_eq_mul] at key
  exact mul_left_cancel₀ hs key


theorem cmp_hyp [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R) (hs : s ≠ 0)
    (hh : (h.map σ)ᵀ * A * h = s • A') (c₁ c₂ : R) (hc : σ c₁ * c₂ = s)
    (x₁ y₁ v₁ w₁ : ι → R) (hv : h *ᵥ v₁ = c₁ • x₁) (hw : h *ᵥ w₁ = c₂ • y₁)
    (hxx : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ x₁) = 0) (hyy : (fun i => σ (y₁ i)) ⬝ᵥ (A *ᵥ y₁) = 0)
    (hxy : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ y₁) = 1) :
    (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ v₁) = 0 ∧ (fun i => σ (w₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 0 ∧
      (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 1 := by
  refine ⟨cmp_gram_pre σ A A' h s hs hh v₁ v₁ x₁ x₁ c₁ c₁ 0 hv hv (by rw [hxx]; ring),
    cmp_gram_pre σ A A' h s hs hh w₁ w₁ y₁ y₁ c₂ c₂ 0 hw hw (by rw [hyy]; ring),
    cmp_gram_pre σ A A' h s hs hh v₁ w₁ x₁ y₁ c₁ c₂ 1 hv hw (by rw [hxy, hc]; ring)⟩

private lemma mapMul_lemma_2 {α β γ : Type*} [Fintype β] (X : Matrix α β R) (Y : Matrix β γ R) :
    (X * Y).map σ = X.map σ * Y.map σ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem cmp_split [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (c₁ c₂ : R) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (x y v₁ w₁ : ι → R)
    (hv : h *ᵥ v₁ = c₁ • x) (hw : h *ᵥ w₁ = c₂ • y)
    (u u' : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ A₁' : Matrix κ κ R)
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu0 : ∀ i, u i (.inl 0) = x i) (hu1 : ∀ i, u i (.inl 1) = y i)
    (hu0' : ∀ i, u' i (.inl 0) = v₁ i) (hu1' : ∀ i, u' i (.inl 1) = w₁ i)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks !![0, 1; 1, 0] 0 0 A₁') :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal ![c₁, c₂]) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = v * h * u' := ⟨_, rfl⟩
  have hcol : ∀ b : Fin 2, ∀ i, (h * u') i (.inl b) = ![c₁, c₂] b * u i (.inl b) := by
    rw [Fin.forall_fin_two]
    constructor
    · intro i
      have e := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu0', hu0, e]
    · intro i
      have e := congrFun hw i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu1', hu1, e]
  have hM1 : ∀ a (b : Fin 2), M a (.inl b) =
      ![c₁, c₂] b * (1 : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) a (.inl b) := by
    intro a b
    rw [hMdef, Matrix.mul_assoc, Matrix.mul_apply, ← hvu, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol b i]
    ring
  have hUM : u * M = h * u' := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hGram : (M.map σ)ᵀ * fromBlocks !![0, 1; 1, 0] 0 0 A₁ * M =
      s • fromBlocks !![0, 1; 1, 0] 0 0 A₁' := by
    rw [← hG, ← hG']
    calc (M.map σ)ᵀ * ((u.map σ)ᵀ * A * u) * M = ((u * M).map σ)ᵀ * A * (u * M) := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hUM]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  have hMb : M = fromBlocks (diagonal ![c₁, c₂]) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rw [hM1 (.inl a) b]
      by_cases hab : a = b
      · subst hab
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hab]
    · simp [Matrix.toBlocks₁₂]
    · rw [hM1 (.inr a) b]
      simp [Matrix.one_apply]
    · simp [Matrix.toBlocks₂₂]
  rw [hMb] at hGram
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero, map_zero, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero] at hGram
  obtain ⟨-, hQ, -, hS⟩ := Matrix.fromBlocks_inj.mp hGram
  have hc₁' : σ c₁ ≠ 0 := by simpa using hc₁
  have hc₂' : σ c₂ ≠ 0 := by simpa using hc₂
  have hB : M.toBlocks₁₂ = 0 := by
    ext a l
    have e0 := congrFun (congrFun hQ 0) l
    have e1 := congrFun (congrFun hQ 1) l
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc₁', hc₂'] at e0 e1
    fin_cases a
    · simpa using e1
    · simpa using e0
  refine ⟨M.toBlocks₂₂, ?_, ?_⟩
  · rw [← hMdef]
    nth_rewrite 1 [hMb]
    rw [hB]
  · rw [hB] at hS
    simpa using hS



end PI.SqPair.LocCartanPairW

namespace PI.SqPair.LCP

open PI.SqPair.LocCartanPairW

theorem inert_isLocalRing {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R} {ϖ : R}
    (hI : Inert R₀ ϖ) : IsLocalRing R := by
  haveI := hI.dom
  have key : ∀ x : R, ¬ IsUnit x → ϖ ∣ x := by
    intro x hx
    by_cases h0 : x = 0
    · exact ⟨0, by rw [h0, mul_zero]⟩
    · obtain ⟨m, u, hu, rfl⟩ := hI.val x h0
      cases m with
      | zero => exact absurd (by simpa using hu) hx
      | succ k => exact ⟨ϖ ^ k * u, by ring⟩
  have back : ∀ x : R, ϖ ∣ x → ¬ IsUnit x := by
    rintro x ⟨c, rfl⟩ hu
    exact hI.pi_nonunit (isUnit_of_mul_isUnit_left hu)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  exact back _ (dvd_add (key a ha) (key b hb))

theorem split_of (hS : SplitOff) : Split := by
  intro R _ _ R₀ ϖ hI κ _ _ A A' h k a hP hak x y v w hxx hyy hxy hv hw
  have := hI.dom
  have : IsLocalRing R := inert_isLocalRing hI
  obtain ⟨⟨hAh, -⟩, ⟨hAh', -⟩, hh⟩ := hP
  have hϖ : star ϖ = ϖ := (hI.fix ϖ).mp hI.pi_mem
  have hcard : Fintype.card κ + 2 = Fintype.card (Fin 2 ⊕ κ) := by
    simp [Fintype.card_sum, add_comm]
  obtain ⟨u, ui, A₁, huv, hvu, hu0, hu1, hG⟩ := hS R (Fin 2 ⊕ κ) κ hcard A hAh x y hxx hyy hxy
  have hs : ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hI.pi_ne
  have hc : (starRingAut : R ≃+* R) (ϖ ^ (k - a)) * ϖ ^ (k + a) = ϖ ^ (2 * k) := by
    rw [map_pow, starRingAut_apply, hϖ, ← pow_add]
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := cmp_hyp (starRingAut : R ≃+* R) A A' h _ hs hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    hc x y v w hv hw hxx hyy hxy
  obtain ⟨u', ui', A₁', huv', -, hu0', hu1', hG'⟩ :=
    hS R (Fin 2 ⊕ κ) κ hcard A' hAh' v w h1 h2 h3
  obtain ⟨h₂, hM, -⟩ := cmp_split (starRingAut : R ≃+* R) A A' h _ hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    (pow_ne_zero _ hI.pi_ne) (pow_ne_zero _ hI.pi_ne) x y v w hv hw u u' ui A₁ A₁' huv hvu hu0 hu1
    hu0' hu1' hG hG'
  refine ⟨u, u', A₁, A₁', h₂, ![ϖ ^ (k - a), ϖ ^ (k + a)], isUnit_det_of_right_inverse huv,
    isUnit_det_of_right_inverse huv', hG, hG', ?_⟩
  rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]

end PI.SqPair.LCP
end
end

section
noncomputable section

open Matrix

namespace PI.LocCartanPair

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_entry {ι m n : Type} [Fintype ι] (A : Matrix ι ι R) (M : Matrix ι m R)
    (N : Matrix ι n R) (r : m) (s : n) :
    (Mᴴ * A * N) r s = star (fun i => M i r) ⬝ᵥ (A *ᵥ fun i => N i s) := by
  rw [Matrix.mul_assoc]; rfl

theorem splPlane_herm {ι : Type} [Fintype ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (a b : ι → R) :
    star (star a ⬝ᵥ (A *ᵥ b)) = star b ⬝ᵥ (A *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec, hA]

theorem splPlane_unitEntry [IsLocalRing R] {ι : Type} [Fintype ι] (w z : ι → R)
    (h : w ⬝ᵥ z = 1) : ∃ i, IsUnit (z i) := by
  by_contra hn
  push Not at hn
  have hm : w ⬝ᵥ z ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hn i))
  rw [h] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def splBasis (E : Fin 2 ⊕ κ ≃ ι) (x y : ι → R) : Matrix ι (Fin 2 ⊕ κ) R :=
  fun i c => Sum.elim (fun a => ![x, y] a i) (fun j => (1 : Matrix ι ι R) i (E (.inr j))) c

def splCorr (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (x y : ι → R) : Matrix (Fin 2) κ R :=
  fun a j => ![-(star y ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j)))),
    -(star x ⬝ᵥ (A *ᵥ fun i => (1 : Matrix ι ι R) i (E (.inr j))))] a

theorem splPlane_core (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (hA : Aᴴ = A) (x y : ι → R)
    (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1)
    (hdet : IsUnit (x (E (.inl 0)) * y (E (.inl 1)) - y (E (.inl 0)) * x (E (.inl 1)))) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  set u₀ := splBasis E x y with hu₀def
  set B := splCorr E A x y with hBdef
  set T : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 B 0 1 with hTdef
  set T' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := fromBlocks 1 (-B) 0 1 with hT'def
  have hTT' : T * T' = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  have hT'T : T' * T = 1 := by simp [hTdef, hT'def, fromBlocks_multiply, fromBlocks_one]
  set S : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u₀.submatrix E id with hSdef
  have hS : S = fromBlocks S.toBlocks₁₁ 0 S.toBlocks₂₁ 1 := by
    conv_lhs => rw [← fromBlocks_toBlocks S]
    congr 1
    · ext a j; simp [hSdef, hu₀def, splBasis, toBlocks₁₂, one_apply]
    · ext k j; simp [hSdef, hu₀def, splBasis, toBlocks₂₂, one_apply]
  have hSdet : IsUnit S.det := by
    rw [hS, det_fromBlocks_zero₁₂, det_one, mul_one, det_fin_two]
    simpa [hSdef, hu₀def, splBasis, toBlocks₁₁] using hdet
  set v₀ : Matrix (Fin 2 ⊕ κ) ι R := S⁻¹.submatrix id E.symm with hv₀def
  have hu₀S : u₀ = S.submatrix E.symm id := by ext i c; simp [hSdef]
  have huv₀ : u₀ * v₀ = 1 := by
    rw [hu₀S, hv₀def, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      mul_nonsing_inv _ hSdet, submatrix_one_equiv]
  have hvu₀ : v₀ * u₀ = 1 := by
    rw [hu₀S, hv₀def, submatrix_mul_equiv, nonsing_inv_mul _ hSdet, submatrix_id_id]
  set u := u₀ * T with hudef
  set v := T' * v₀ with hvdef
  have huv : u * v = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc T, hTT', Matrix.one_mul, huv₀]
  have hvu : v * u = 1 := by
    rw [hudef, hvdef, Matrix.mul_assoc, ← Matrix.mul_assoc v₀, hvu₀, Matrix.one_mul, hT'T]
  have hc0 : (fun i => u i (.inl 0)) = x := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hc1 : (fun i => u i (.inl 1)) = y := by
    funext i; simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  have hcj : ∀ j, (fun i => u i (.inr j)) = (fun i => (1 : Matrix ι ι R) i (E (.inr j)))
      + B 0 j • x + B 1 j • y := by
    intro j; funext i
    simp [hudef, hTdef, hu₀def, splBasis, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, one_apply]
    ring
  set G := uᴴ * A * u with hGdef
  have hG : ∀ r s, G r s = star (fun i => u i r) ⬝ᵥ (A *ᵥ fun i => u i s) :=
    fun r s => splPlane_entry A u u r s
  have h12 : G.toBlocks₁₂ = 0 := by
    ext a j
    simp only [toBlocks₁₂, of_apply, hG, hcj, Matrix.zero_apply]
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, hc0, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hxx, hxy, hBdef, splCorr]
      simp
    · simp only [Fin.mk_one, Fin.isValue, hc1, mulVec_add, mulVec_smul, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hyx, hyy, hBdef, splCorr]
      simp
  have h21 : G.toBlocks₂₁ = 0 := by
    ext j a
    have := congrFun (congrFun h12 a) j
    simp only [toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply] at this ⊢
    rw [hG, ← splPlane_herm A hA, ← hG, this, star_zero]
  have h11 : G.toBlocks₁₁ = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [toBlocks₁₁, hG, hc0, hc1, hxx, hyy, hxy, hyx]
  have hGe : G = fromBlocks !![0, 1; 1, 0] 0 0 G.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [h11, h12, h21]
  refine ⟨u, v, G.toBlocks₂₂, huv, hvu, fun i => congrFun hc0 i, fun i => congrFun hc1 i,
    hGe, ?_, ?_⟩
  · ext i j
    simp only [conjTranspose_apply, toBlocks₂₂, of_apply]
    rw [hG, hG, splPlane_herm A hA]
  · intro hAdet
    set U : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R := u.submatrix E id with hUdef
    have hUv : U * v.submatrix id E = 1 := by
      rw [hUdef, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, huv,
        submatrix_one_equiv]
    have hU : IsUnit U.det := isUnit_det_of_right_inverse hUv
    have hGU : G = Uᴴ * A.submatrix E E * U := by
      rw [hUdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
        submatrix_id_id]
    have hGdet : IsUnit G.det := by
      rw [hGU, det_mul, det_mul, det_conjTranspose, det_submatrix_equiv_self]
      exact (hU.star.mul hAdet).mul hU
    rw [hGe, det_fromBlocks_zero₁₂] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet

section Local

variable {R : Type} [CommRing R] [StarRing R]

theorem splPlane_pair [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : Aᴴ = A) (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ i₀ j₀, i₀ ≠ j₀ ∧ IsUnit (x i₀ * y j₀ - y i₀ * x j₀) := by
  have hyx : star y ⬝ᵥ (A *ᵥ x) = 1 := by rw [← splPlane_herm A hA x y, hxy, star_one]
  rw [dotProduct_mulVec] at hyx
  obtain ⟨i₀, hi₀⟩ := splPlane_unitEntry _ _ hyx
  obtain ⟨xi, hxi⟩ := hi₀.exists_right_inv
  set y' := y - (y i₀ * xi) • x with hy'
  have hy'i : y' i₀ = 0 := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(y i₀)) * hxi
  have hxy' : (star x ᵥ* A) ⬝ᵥ y' = 1 := by
    rw [← dotProduct_mulVec, hy', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxx,
      hxy, smul_eq_mul, mul_zero, sub_zero]
  obtain ⟨j₀, hj₀⟩ := splPlane_unitEntry _ _ hxy'
  have hne : i₀ ≠ j₀ := by
    rintro rfl; rw [hy'i] at hj₀; exact not_isUnit_zero hj₀
  refine ⟨i₀, j₀, hne, ?_⟩
  have e : x i₀ * y j₀ - y i₀ * x j₀ = x i₀ * y' j₀ := by
    simp only [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y i₀ * x j₀) * hxi
  rw [e]; exact hi₀.mul hj₀

def splEquiv {ι : Type} [DecidableEq ι] (i₀ j₀ : ι) (hne : i₀ ≠ j₀) :
    Fin 2 ⊕ {j // j ≠ i₀ ∧ j ≠ j₀} ≃ ι where
  toFun := Sum.elim ![i₀, j₀] Subtype.val
  invFun j := if h0 : j = i₀ then .inl 0 else if h1 : j = j₀ then .inl 1 else .inr ⟨j, h0, h1⟩
  left_inv := by
    rintro (a | ⟨j, h0, h1⟩)
    · fin_cases a
      · simp
      · simp [hne.symm]
    · simp [h0, h1]
  right_inv := by
    intro j
    by_cases h0 : j = i₀
    · subst h0; simp
    · by_cases h1 : j = j₀
      · subst h1; simp [h0]
      · simp [h0, h1]

theorem splPlane [IsLocalRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hc : Fintype.card κ + 2 = Fintype.card ι) (A : Matrix ι ι R) (hA : Aᴴ = A)
    (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  obtain ⟨i₀, j₀, hne, hu⟩ := splPlane_pair A hA x y hxx hxy
  have hc₀ : Fintype.card {j // j ≠ i₀ ∧ j ≠ j₀} = Fintype.card κ := by
    have := Fintype.card_congr (splEquiv i₀ j₀ hne)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  let E : Fin 2 ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivOfCardEq hc₀).symm).trans (splEquiv i₀ j₀ hne)
  have h0 : E (.inl 0) = i₀ := by simp [E, splEquiv]
  have h1 : E (.inl 1) = j₀ := by simp [E, splEquiv]
  exact splPlane_core E A hA x y hxx hyy hxy (by rw [h0, h1]; exact hu)

end Local

end PI.LocCartanPair
end
end

section
noncomputable section

namespace PI.SqPair.LCP

theorem split_off_hyperbolic : SplitOff := by
  intro R _ _ _ ι κ _ _ _ _ hc A hA x y hxx hyy hxy
  obtain ⟨u, v, A₁, h1, h2, h3, h4, h5, -, -⟩ := PI.LocCartanPair.splPlane hc A hA x y hxx hyy hxy
  exact ⟨u, v, A₁, h1, h2, h3, h4, h5⟩

end PI.SqPair.LCP
end
end

section
namespace PI.SqPair.LCP

theorem pair_split' : Split := split_of split_off_hyperbolic

end PI.SqPair.LCP
end
