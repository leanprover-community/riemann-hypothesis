import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

namespace Formalism.FourierDecayAlt.P.S3x5

open Finset Formalism.FourierDecayAlt.S3




theorem eta_pow (η : ℤ) (hη : η = 1 ∨ η = -1) (i : ℤ) : ((η : ℝ) ^ i = 1 ∨ (η : ℝ) ^ i = -1) := by
  rcases hη with rfl | rfl
  · left; simp
  · rcases Int.even_or_odd i with h | h
    · left; push_cast; exact h.neg_one_zpow
    · right; push_cast; exact h.neg_one_zpow

theorem factor_bounds (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (_hi : 1 ≤ i) :
    1 - (q : ℝ) ^ (-i) ≤ 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ∧
      1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) ≤ 1 + (q : ℝ) ^ (-i) := by
  have hpos : 0 < (q : ℝ) ^ (-i) := zpow_pos (by exact_mod_cast (by omega : 0 < q)) _
  rcases eta_pow η hη i with h | h <;> rw [h] <;> constructor <;> linarith



theorem geom_le (q : ℕ) (hq : 2 ≤ q) (a b : ℤ) :
    ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) ≤ 2 * (q : ℝ) ^ (-a) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  rcases lt_or_ge b a with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have key : ∀ b : ℤ, a ≤ b →
        ∑ i ∈ Finset.Icc a b, (q : ℝ) ^ (-i) + (q : ℝ) ^ (-b) ≤ 2 * (q : ℝ) ^ (-a) := by
      intro b hb
      induction b, hb using Int.leInduction with
      | base => simp; linarith
      | succ b hb ih =>
        have e : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [e, Finset.sum_insert (by simp)]
        have e2 : (q : ℝ) ^ (-b) = (q : ℝ) ^ (-(b + 1)) * q := by
          rw [← zpow_add_one₀ hq0.ne']; congr 1; ring
        have hp : 0 < (q : ℝ) ^ (-(b + 1)) := zpow_pos hq0 _
        nlinarith
    have := key b h
    have hp : 0 < (q : ℝ) ^ (-b) := zpow_pos hq0 _
    linarith




end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5






end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Polynomial Formalism.FourierDecayAlt.S3

@[reducible] def starRingOfCard (K : Type) [Field K] [Fintype K] (q : ℕ) (hc : Fintype.card K = q ^ 2) :
    StarRing K where
  star x := x ^ q
  star_involutive x := by
    show (x ^ q) ^ q = x
    rw [← pow_mul, ← sq, ← hc, FiniteField.pow_card]
  star_mul x y := by
    show (x * y) ^ q = y ^ q * x ^ q
    rw [mul_pow, mul_comm]
  star_add x y := by
    show (x + y) ^ q = x ^ q + y ^ q
    obtain ⟨p, hp⟩ := CharP.exists K
    obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
    have : Fact p.Prime := ⟨hpp⟩
    have hd : q ∣ p ^ (n : ℕ) := by rw [← hn, hc]; exact dvd_pow_self q (by norm_num)
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hpp).1 hd
    exact add_pow_char_pow x y p m

variable {K : Type} [Field K] [Fintype K]

theorem two_le_q {q : ℕ} (hc : Fintype.card K = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := K)
  rw [hc] at h
  by_contra hq
  have : q = 0 ∨ q = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h

theorem card_root_le (p : K[X]) (hp : p ≠ 0) : Nat.card {x : K // p.eval x = 0} ≤ p.natDegree := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc _ ≤ p.roots.toFinset.card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
        exact hx)
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ _ := Polynomial.card_roots' p

theorem card_pm_le {q : ℕ} (hq : 2 ≤ q) (e : K) : Nat.card {x : K // x ^ q + e * x = 0} ≤ q := by
  have hdeg : (C e * X : K[X]).degree < (q : ℕ) := by
    calc (C e * X : K[X]).degree ≤ 1 := by
          refine (Polynomial.degree_C_mul_X_le e)
      _ < (q : ℕ) := by exact_mod_cast (by omega : 1 < q)
  have hm : (X ^ q + C e * X : K[X]).Monic := Polynomial.monic_X_pow_add hdeg
  have hn : (X ^ q + C e * X : K[X]).natDegree = q := by
    have : (X ^ q + C e * X : K[X]).degree = (q : ℕ) := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  have := card_root_le _ hm.ne_zero
  rw [hn] at this
  simpa using this

variable [StarRing K]


theorem exists_trace_ne {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) :
    ∃ μ : K, μ + star μ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hq := two_le_q hc
  have h1 := card_pm_le (K := K) hq 1
  have h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card K := by
    apply Nat.card_congr
    exact Equiv.subtypeUnivEquiv (fun x => by have := hcon x; rw [hs] at this; rw [one_mul, add_comm]; exact this)
  rw [h2, Nat.card_eq_fintype_card, hc] at h1
  nlinarith


theorem norm_surj {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (t : K) (ht : t ≠ 0) (hst : star t = t) : ∃ l : K, star l * l = t := by
  classical
  have hq := two_le_q hc
  have hcardU : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hc]
    obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = s * (s + 1 + 1) + 1 := by ring
    omega
  have h1 : Nat.card (powMonoidHom (q + 1) : Kˣ →* Kˣ).range = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_range, hcardU, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ (by omega)]
  have h2 : Nat.card (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right (Dvd.intro _ rfl)]
  have hle : (powMonoidHom (q + 1) : Kˣ →* Kˣ).range ≤ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hcardU]
    exact pow_card_eq_one'
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h1, h2])
  have hmem : Units.mk0 t ht ∈ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [hs] at hst
    have : t ^ (q - 1) * t = 1 * t := by
      rw [← pow_succ, one_mul, Nat.sub_add_cancel (by omega)]; exact hst
    exact mul_right_cancel₀ ht this
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : K), ?_⟩
  rw [hs, ← pow_succ]
  have := congrArg Units.val hx
  simpa using this


end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix

variable {K : Type} [Field K] [Fintype K] [StarRing K]

theorem polar (htr : ∃ μ : K, μ + star μ ≠ 0) {ν : Type} [Fintype ν] [DecidableEq ν]
    (J : Matrix ν ν K) (hJ : Jᴴ = J) (W : Submodule K (Matrix ν Unit K))
    (h0 : ∀ v ∈ W, vᴴ * J * v = 0) : ∀ u ∈ W, ∀ v ∈ W, uᴴ * J * v = 0 := by
  intro u hu v hv
  obtain ⟨μ, hμ⟩ := htr
  by_contra hne
  have hz0 : (uᴴ * J * v) () () ≠ 0 := by
    intro h
    apply hne
    ext i j
    exact h
  have hvu : vᴴ * J * u = (uᴴ * J * v)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have h1 := h0 (u + (μ / (uᴴ * J * v) () ()) • v) (W.add_mem hu (W.smul_mem _ hv))
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, h0 u hu, h0 v hv, hvu] at h1
  have h2 := congrFun (congrFun h1 ()) ()
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, conjTranspose_apply, smul_eq_mul,
    zero_add, mul_zero, add_zero] at h2
  apply hμ
  rw [← star_mul', div_mul_cancel₀ _ hz0] at h2
  rw [add_comm]
  exact h2

theorem gram_submatrix {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (Z : Matrix ν α K) (e : β → α) :
    (Z.submatrix id e)ᴴ * J * (Z.submatrix id e) = (Zᴴ * J * Z).submatrix e e := by
  ext i j
  rfl

theorem exists_frame (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {ν : Type} [Fintype ν] [DecidableEq ν] (J : Matrix ν ν K) (hJ : Jᴴ = J) (hd : IsUnit J.det)
    (m : ℕ) (hm : m ≤ Fintype.card ν) : ∃ X : Matrix ν (Fin m) K, Xᴴ * J * X = 1 := by
  induction m with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ m ih =>
    obtain ⟨X, hX⟩ := ih (by omega)
    let f : Matrix ν Unit K →ₗ[K] Matrix (Fin m) Unit K :=
      { toFun := fun Y => Xᴴ * J * Y
        map_add' := fun a b => Matrix.mul_add _ _ _
        map_smul' := fun c a => by simp }
    have hf : ∀ Y, f Y = Xᴴ * J * Y := fun _ => rfl
    have hker : LinearMap.ker f ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_matrix, Module.finrank_matrix]
      simp
      omega
    obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff _).1 hker
    have hex : ∃ v ∈ LinearMap.ker f, vᴴ * J * v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hp := polar htr J hJ _ hcon
      apply hy0
      have hyX : Xᴴ * J * y = 0 := by rw [← hf]; exact hyW
      have hyJ : ∀ z : Matrix ν Unit K, yᴴ * J * z = 0 := by
        intro z
        have hz' : z - X * (Xᴴ * J * z) ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf, Matrix.mul_sub, ← Matrix.mul_assoc (Xᴴ * J) X, hX, Matrix.one_mul,
            sub_self]
        have h1 := hp y hyW _ hz'
        have h2 : yᴴ * J * X = 0 := by
          have h3 : (Xᴴ * J * y)ᴴ = 0 := by rw [hyX]; simp
          rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
            ← Matrix.mul_assoc] at h3
        rw [Matrix.mul_sub, ← Matrix.mul_assoc (yᴴ * J) X, h2, Matrix.zero_mul, sub_zero] at h1
        exact h1
      have hyJ0 : yᴴ * J = 0 := by
        ext a i
        have h4 := congrFun (congrFun (hyJ (Matrix.single i () 1)) a) ()
        simpa using h4
      have hJy : J * y = 0 := by
        have h5 := congrArg conjTranspose hyJ0
        rwa [conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_zero] at h5
      calc y = J⁻¹ * (J * y) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = 0 := by rw [hJy, Matrix.mul_zero]
    obtain ⟨v, hvW, hv0⟩ := hex
    have hvX : Xᴴ * J * v = 0 := by rw [← hf]; exact hvW
    have ht0 : (vᴴ * J * v) () () ≠ 0 := by
      intro h
      apply hv0
      ext i j
      exact h
    have hherm : (vᴴ * J * v)ᴴ = vᴴ * J * v := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
    have hst : star ((vᴴ * J * v) () ()) = (vᴴ * J * v) () () := by
      have h6 := congrFun (congrFun hherm ()) ()
      rwa [conjTranspose_apply] at h6
    obtain ⟨l, hl⟩ := hnorm ((vᴴ * J * v) () ())⁻¹ (inv_ne_zero ht0) (by rw [star_inv₀, hst])
    have hw1 : (l • v)ᴴ * J * (l • v) = 1 := by
      ext i j
      simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm l, hl, inv_mul_cancel₀ ht0]
      simp
    have hw2 : Xᴴ * J * (l • v) = 0 := by rw [Matrix.mul_smul, hvX, smul_zero]
    have hw3 : (l • v)ᴴ * J * X = 0 := by
      have h3 : (Xᴴ * J * (l • v))ᴴ = 0 := by rw [hw2]; simp
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
        ← Matrix.mul_assoc] at h3
    let e : Fin m ⊕ Unit ≃ Fin (m + 1) := Fintype.equivOfCardEq (by simp)
    refine ⟨(Matrix.fromCols X (l • v)).submatrix id e.symm, ?_⟩
    rw [gram_submatrix, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      fromRows_mul_fromCols, hX, hw1, hw2, hw3, fromBlocks_one, submatrix_one_equiv]

theorem exists_G (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {μ ν : Type} [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (hcard : Fintype.card μ = Fintype.card ν) (J : Matrix μ μ K) (D : Matrix ν ν K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hD : Dᴴ = D) (hdD : IsUnit D.det) :
    ∃ (G : Matrix μ ν K) (G' : Matrix ν μ K), G * G' = 1 ∧ G' * G = 1 ∧ Gᴴ * J * G = D := by
  obtain ⟨X, hX⟩ := exists_frame htr hnorm J hJ hdJ (Fintype.card μ) le_rfl
  obtain ⟨Y, hY⟩ := exists_frame htr hnorm D hD hdD (Fintype.card μ) hcard.le
  have hX' : X * (Xᴴ * J) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp)).1 hX
  have hY' : Y * (Yᴴ * D) = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hcard])).1 hY
  refine ⟨X * (Yᴴ * D), Y * (Xᴴ * J), ?_, ?_, ?_⟩
  · calc X * (Yᴴ * D) * (Y * (Xᴴ * J)) = X * (Yᴴ * D * Y) * (Xᴴ * J) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hX']
  · calc Y * (Xᴴ * J) * (X * (Yᴴ * D)) = Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hX, Matrix.mul_one, hY']
  · calc (X * (Yᴴ * D))ᴴ * J * (X * (Yᴴ * D)) = D * Y * (Xᴴ * J * X) * (Yᴴ * D) := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
      _ = D * (Y * (Yᴴ * D)) := by rw [hX, Matrix.mul_one, Matrix.mul_assoc]
      _ = D := by rw [hY', Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
theorem star_vecMul_zero {α κ : Type} [Fintype α] (M : Matrix α κ K) (u : α → K)
    (h : Mᴴ *ᵥ u = 0) : star u ᵥ* M = 0 := by
  have h1 := Matrix.mulVec_conjTranspose M u
  rw [h] at h1
  have h2 := congrArg star h1
  simpa using h2.symm

omit [Fintype K] in
theorem exists_B (a : ℕ) (T : Matrix (Fin a) (Fin a) K) (hT : Tᴴ = T) :
    ∃ B : Matrix (Fin a) (Fin (a - T.rank)) K,
      ∀ D : Matrix (Fin (a - T.rank)) (Fin (a - T.rank)) K,
        IsUnit (Matrix.fromBlocks T B Bᴴ D).det := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range T.mulVecLin)
  have hfin : Module.finrank K C = a - T.rank := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K (LinearMap.range T.mulVecLin) = T.rank := rfl
    omega
  let b := Module.finBasisOfFinrankEq K C hfin
  let B : Matrix (Fin a) (Fin (a - T.rank)) K := Matrix.of fun i j => (b j : Fin a → K) i
  have hBv : ∀ w : Fin (a - T.rank) → K, B *ᵥ w = ((∑ j, w j • b j : C) : Fin a → K) := by
    intro w
    ext i
    simp [B, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨B, fun D => ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ x, (Matrix.fromBlocks T B Bᴴ D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.fromBlocks_mulVec] at hx
    set u : Fin a → K := x ∘ Sum.inl with hu
    set w : Fin (a - T.rank) → K := x ∘ Sum.inr with hw
    have h1 : T *ᵥ u + B *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inl i)
      simpa using this
    have h2 : Bᴴ *ᵥ u + D *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inr i)
      simpa using this
    have hTR : T *ᵥ u ∈ LinearMap.range T.mulVecLin := ⟨u, by simp⟩
    have hBC : B *ᵥ w ∈ C := by rw [hBv]; exact Submodule.coe_mem _
    have hTC : T *ᵥ u ∈ C := by
      have : T *ᵥ u = -(B *ᵥ w) := eq_neg_of_add_eq_zero_left h1
      rw [this]; exact C.neg_mem hBC
    have hTu : T *ᵥ u = 0 := Submodule.disjoint_def.1 hC.disjoint _ hTR hTC
    have hBw : B *ᵥ w = 0 := by rw [hTu, zero_add] at h1; exact h1
    have hw0 : w = 0 := by
      rw [hBv] at hBw
      have h3 : (∑ j, w j • b j : C) = 0 := Subtype.ext hBw
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent w h3 j
    have hBu : Bᴴ *ᵥ u = 0 := by rw [hw0, Matrix.mulVec_zero, add_zero] at h2; exact h2
    have k1 : star u ᵥ* T = 0 := star_vecMul_zero T u (by rw [hT]; exact hTu)
    have k2 : star u ᵥ* B = 0 := star_vecMul_zero B u hBu
    have hsu : star u = 0 := by
      apply _root_.dotProduct_eq_zero
      intro y
      have hy : y ∈ LinearMap.range T.mulVecLin ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨r, ⟨x', rfl⟩, c', hc', rfl⟩ := Submodule.mem_sup.1 hy
      have hc2 : c' = B *ᵥ (fun j => b.repr ⟨c', hc'⟩ j) := by
        rw [hBv, b.sum_repr]
      rw [dotProduct_add, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, k1, hc2,
        Matrix.dotProduct_mulVec, k2]
      simp
    have hu0 : u = 0 := by simpa using congrArg star hsu
    funext i
    rcases i with i | i
    · exact congrFun hu0 i
    · exact congrFun hw0 i
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

omit [StarRing K] in
theorem card_fibre {n a c : ℕ} (A : Matrix (Fin a) (Fin n) K) (hA : A.rank = a)
    (B : Matrix (Fin a) (Fin c) K) :
    Nat.card {Y : Matrix (Fin n) (Fin c) K // A * Y = B} = Fintype.card K ^ ((n - a) * c) := by
  classical
  have hsurj : Function.Surjective A.mulVec := by
    have h1 : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]; exact hA
    intro y
    have hy : y ∈ LinearMap.range A.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by simpa using hx⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  let φ : Matrix (Fin n) (Fin c) K →ₗ[K] Matrix (Fin a) (Fin c) K :=
    { toFun := fun Y => A * Y
      map_add' := fun x y => Matrix.mul_add A x y
      map_smul' := fun r x => by simp }
  have hφa : ∀ Y, φ Y = A * Y := fun _ => rfl
  have hφ : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.2 (fun Z => ⟨R * Z, by rw [hφa, ← Matrix.mul_assoc, hR, Matrix.one_mul]⟩)
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφ, finrank_top, Module.finrank_matrix, Module.finrank_matrix] at hdim
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hdim
  have hker : Module.finrank K (LinearMap.ker φ) = (n - a) * c := by rw [Nat.sub_mul]; omega
  let e : {Y : Matrix (Fin n) (Fin c) K // A * Y = B} ≃ LinearMap.ker φ :=
    { toFun := fun Y => ⟨Y.1 - R * B, by
        rw [LinearMap.mem_ker, hφa, Matrix.mul_sub, Y.2, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]⟩
      invFun := fun Z => ⟨Z.1 + R * B, by
        have hz : A * Z.1 = 0 := Z.2
        rw [Matrix.mul_add, hz, ← Matrix.mul_assoc, hR, Matrix.one_mul, zero_add]⟩
      left_inv := fun Y => by simp
      right_inv := fun Z => by simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hker]

end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
theorem gram_reindex {ν ν' α α' : Type} [Fintype ν] [Fintype ν'] (e : ν' ≃ ν) (f : α' → α)
    (J : Matrix ν ν K) (Z : Matrix ν α K) :
    (Z.submatrix e f)ᴴ * J.submatrix e e * Z.submatrix e f = (Zᴴ * J * Z).submatrix f f := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

omit [Fintype K] in
theorem unit_of_gram {ν : Type} [Fintype ν] [DecidableEq ν] (J g : Matrix ν ν K) (hd : IsUnit J.det)
    (h : gᴴ * J * g = J) : IsUnit g.det := by
  have : IsUnit ((gᴴ * J).det * g.det) := by rw [← det_mul, h]; exact hd
  exact isUnit_of_mul_isUnit_right this


omit [Fintype K] in
theorem witt_gen
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α] (J : Matrix ν ν K)
    (X Y : Matrix ν α K) (hJ : Jᴴ = J) (hd : IsUnit J.det) (hX : X.rank = Fintype.card α)
    (hY : Y.rank = Fintype.card α) (h : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix ν ν K, gᴴ * J * g = J ∧ g * X = Y := by
  set e := Fintype.equivFin ν
  set f := Fintype.equivFin α
  obtain ⟨g, hg1, hg2⟩ := hW _ _ (J.submatrix e.symm e.symm) (X.submatrix e.symm f.symm)
    (Y.submatrix e.symm f.symm) (by rw [conjTranspose_submatrix, hJ])
    (by rw [det_submatrix_equiv_self]; exact hd) (by rw [rank_submatrix, hX]) (by rw [rank_submatrix, hY])
    (by rw [gram_reindex, gram_reindex, h])
  refine ⟨g.submatrix e e, ?_, ?_⟩
  · have h1 := gram_reindex e e (J.submatrix e.symm e.symm) g
    rw [hg1] at h1
    simpa using h1
  · have h2 := congrArg (fun M => M.submatrix e f) hg2
    simp only [← submatrix_mul_equiv g _ e e f] at h2
    simpa using h2

omit [Fintype K] in
theorem stab_form {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hdT : IsUnit T.det)
    (k : Matrix (α ⊕ β) (α ⊕ β) K) (h1 : k * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) =
      (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K))
    (h2 : kᴴ * fromBlocks T 0 0 T' * k = fromBlocks T 0 0 T') :
    ∃ d : Matrix β β K, k = fromBlocks 1 0 0 d ∧ dᴴ * T' * d = T' := by
  obtain ⟨A, B, C, d, rfl⟩ : ∃ A B C d, k = fromBlocks A B C d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks k).symm⟩
  rw [fromBlocks_mul_fromRows] at h1
  obtain ⟨hA, hC⟩ := fromRows_inj h1
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at hA hC
  subst hA; subst hC
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h2
  obtain ⟨-, hB, -, hd⟩ := h2
  simp only [conjTranspose_one, Matrix.one_mul, conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hB hd
  have hB0 : B = 0 := by
    have := congrArg (fun M => T⁻¹ * M) hB
    simpa [← Matrix.mul_assoc, nonsing_inv_mul T hdT] using this
  subst hB0
  refine ⟨d, rfl, ?_⟩
  simpa using hd

omit [Fintype K] in
theorem rank_of_gram {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    (J : Matrix ν ν K) (T : Matrix α α K) (hdT : IsUnit T.det) (X : Matrix ν α K)
    (h : Xᴴ * J * X = T) : X.rank = Fintype.card α := by
  apply le_antisymm (rank_le_card_width X)
  have h1 := rank_mul_le_right (Xᴴ * J) X
  rw [h, rank_of_isUnit T ((isUnit_iff_isUnit_det T).2 hdT)] at h1
  exact h1

theorem block_count
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hT : Tᴴ = T) (hdT : IsUnit T.det) (hT' : T'ᴴ = T')
    (hdT' : IsUnit T'.det) :
    Nat.card {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * fromBlocks T 0 0 T' * g = fromBlocks T 0 0 T'} =
      Nat.card {X : Matrix (α ⊕ β) α K // Xᴴ * fromBlocks T 0 0 T' * X = T} *
        Nat.card {d : Matrix β β K // dᴴ * T' * d = T'} := by
  classical
  set J := fromBlocks T 0 0 T' with hJdef
  have hJ : Jᴴ = J := by rw [hJdef, fromBlocks_conjTranspose]; simp [hT, hT']
  have hdJ : IsUnit J.det := by rw [hJdef, det_fromBlocks_zero₂₁]; exact hdT.mul hdT'
  set X0 : Matrix (α ⊕ β) α K := fromRows 1 0 with hX0def
  have hX0 : X0ᴴ * J * X0 = T := by
    rw [hX0def, conjTranspose_fromRows_eq_fromCols_conjTranspose, hJdef, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
    simp
  have hch : ∀ X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T}, ∃ g, gᴴ * J * g = J ∧ g * X0 = X.1 :=
    fun X => witt_gen hW J X0 X.1 hJ hdJ (rank_of_gram J T hdT X0 hX0) (rank_of_gram J T hdT X.1 X.2)
      (by rw [hX0, X.2])
  choose γ hγ1 hγ2 using hch
  have hδ : ∀ d : Matrix β β K, fromBlocks (1 : Matrix α α K) 0 0 d * X0 = X0 := by
    intro d
    rw [hX0def, fromBlocks_mul_fromRows]; simp
  have hδ2 : ∀ d : Matrix β β K, dᴴ * T' * d = T' →
      (fromBlocks (1 : Matrix α α K) 0 0 d)ᴴ * J * fromBlocks (1 : Matrix α α K) 0 0 d = J := by
    intro d hd
    rw [hJdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hd]
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective
    (fun p : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} × {d : Matrix β β K // dᴴ * T' * d = T'} =>
      (⟨γ p.1 * fromBlocks 1 0 0 p.2.1, ?_⟩ : {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * J * g = J})) ⟨?_, ?_⟩
  · rw [conjTranspose_mul]
    calc _ = (fromBlocks (1 : Matrix α α K) 0 0 p.2.1)ᴴ * ((γ p.1)ᴴ * J * γ p.1) *
          fromBlocks (1 : Matrix α α K) 0 0 p.2.1 := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hγ1, hδ2 _ p.2.2]
  · rintro ⟨X, d⟩ ⟨X', d'⟩ h
    have h' : γ X * fromBlocks 1 0 0 d.1 = γ X' * fromBlocks 1 0 0 d'.1 := congrArg Subtype.val h
    have hX : X = X' := by
      apply Subtype.ext
      have := congrArg (fun M => M * X0) h'
      simp only [Matrix.mul_assoc, hδ, hγ2] at this
      exact this
    subst hX
    have hu : IsUnit (γ X) := (isUnit_iff_isUnit_det _).2 (unit_of_gram J _ hdJ (hγ1 X))
    have h3 := hu.mul_left_cancel h'
    rw [fromBlocks_inj] at h3
    have : d = d' := Subtype.ext h3.2.2.2
    rw [this]
  · rintro ⟨h, hh⟩
    have hXg : (h * X0)ᴴ * J * (h * X0) = T := by
      rw [conjTranspose_mul]
      calc _ = X0ᴴ * (hᴴ * J * h) * X0 := by simp only [Matrix.mul_assoc]
        _ = T := by rw [hh, hX0]
    set X : {X : Matrix (α ⊕ β) α K // Xᴴ * J * X = T} := ⟨h * X0, hXg⟩ with hXdef
    have hu : IsUnit (γ X).det := unit_of_gram J _ hdJ (hγ1 X)
    set k := (γ X)⁻¹ * h with hk
    have hγk : γ X * k = h := by rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
    have hk1 : k * X0 = X0 := by
      have e1 : γ X * X0 = h * X0 := hγ2 X
      rw [hk, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    have hk2 : kᴴ * J * k = J := by
      have : (γ X * k)ᴴ * J * (γ X * k) = J := by rw [hγk]; exact hh
      rw [conjTranspose_mul] at this
      calc _ = kᴴ * ((γ X)ᴴ * J * γ X) * k := by rw [hγ1]
        _ = kᴴ * (γ X)ᴴ * J * (γ X * k) := by simp only [Matrix.mul_assoc]
        _ = J := this
    obtain ⟨d, hd1, hd2⟩ := stab_form T T' hdT k hk1 hk2
    refine ⟨(X, ⟨d, hd2⟩), ?_⟩
    apply Subtype.ext
    show γ X * fromBlocks 1 0 0 d = h
    rw [← hd1, hγk]


end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P.S3x5

open Matrix Formalism.FourierDecayAlt.S3

theorem card_of_fibres {P A : Type} [Finite P] [Finite A] (f : P → A) (m : ℝ)
    (h : ∀ a, (Nat.card {p // f p = a} : ℝ) = m) : (Nat.card P : ℝ) = Nat.card A * m := by
  classical
  have := Fintype.ofFinite A
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

variable {K : Type} [Field K] [Fintype K] [StarRing K]

omit [Fintype K] in
theorem rank_conj_mul {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a)
    (J : Matrix (Fin n) (Fin n) K) (hdJ : IsUnit J.det) : (Xᴴ * J).rank = a := by
  have hsurj : Function.Surjective Xᵀ.mulVec := by
    have h1 : LinearMap.range Xᵀ.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      have := rank_transpose X
      rw [hX] at this
      exact this
    intro y
    have hy : y ∈ LinearMap.range Xᵀ.mulVecLin := by rw [h1]; trivial
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by rw [← hx, Matrix.mulVecLin_apply]⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  have h2 : Rᵀ * X = 1 := by
    have := congrArg transpose hR
    simpa [transpose_mul] using this
  have h3 : Xᴴ * Rᵀᴴ = 1 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul] using this
  have h4 : (Xᴴ * J) * (J⁻¹ * Rᵀᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, mul_nonsing_inv _ hdJ, Matrix.one_mul, h3]
  apply le_antisymm
  · simpa using rank_le_card_height (Xᴴ * J)
  · have := rank_mul_le_left (Xᴴ * J) (J⁻¹ * Rᵀᴴ)
    rw [h4, rank_one, Fintype.card_fin] at this
    exact this

omit [Fintype K] in
theorem gram_fromCols {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K) :
    (fromCols X Y)ᴴ * J * fromCols X Y =
      fromBlocks (Xᴴ * J * X) (Xᴴ * J * Y) (Yᴴ * J * X) (Yᴴ * J * Y) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]

omit [Fintype K] in
theorem rank_left_block {ν α β : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K)
    (S : Matrix (α ⊕ β) (α ⊕ β) K) (hS : IsUnit S.det)
    (h : (fromCols X Y)ᴴ * J * fromCols X Y = S) : X.rank = Fintype.card α := by
  have hL : (S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y = 1 := by
    rw [Matrix.mul_assoc, h, nonsing_inv_mul _ hS]
  have hX : X = fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) := by
    rw [fromCols_mul_fromRows]; simp
  have hM : ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) * X = 1 := by
    calc _ = ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (S⁻¹ * ((fromCols X Y)ᴴ * J))) *
          (fromCols X Y * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          rw [← hX]
      _ = (fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
          (((S⁻¹ * ((fromCols X Y)ᴴ * J)) * fromCols X Y) *
            (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K)) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hL, Matrix.one_mul, fromCols_mul_fromRows]
          simp
  apply le_antisymm (rank_le_card_width X)
  have := rank_mul_le_right ((fromCols (1 : Matrix α α K) (0 : Matrix α β K) : Matrix α (α ⊕ β) K) *
      (S⁻¹ * ((fromCols X Y)ᴴ * J))) X
  rw [hM, rank_one] at this
  exact this


end Formalism.FourierDecayAlt.P.S3x5

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5


end Formalism.FourierDecayAlt.P
