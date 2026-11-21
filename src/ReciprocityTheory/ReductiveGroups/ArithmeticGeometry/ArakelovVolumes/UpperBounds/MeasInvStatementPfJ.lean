import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper
import Lemmata.GeneralBFactForm.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix

noncomputable section

theorem det_of_key {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
    (M : Matrix m m R) (κ : m → α) (hκ : Function.Injective κ)
    (h : ∀ i j, κ i < κ j → M i j = 0) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' (fun i => OrderDual.toDual (κ i))
    (fun a b hab => hκ (OrderDual.toDual.injective hab))
  exact Matrix.det_of_upperTriangular (fun i j hij => h i j hij)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev Ix (ι : Type*) (r : ℕ) : Type _ := ι × Fin r × Fin r

def sl (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then w (τ, a, b) else 0

def up (w : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b < a then 0 else w (τ, a, b)

def lu (w : Ix ι r → ℂ) : Ix ι r → ℂ := fun i => ((1 + sl w i.1) * up w i.1) i.2.1 i.2.2

lemma sl_add (h h' : Ix ι r → ℂ) (τ : ι) : sl (h + h') τ = sl h τ + sl h' τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma up_add (h h' : Ix ι r → ℂ) (τ : ι) : up (h + h') τ = up h τ + up h' τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma sl_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : sl (c • h) τ = c • sl h τ := by
  ext a b
  simp only [sl, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma up_smul (c : ℂ) (h : Ix ι r → ℂ) (τ : ι) : up (c • h) τ = c • up h τ := by
  ext a b
  simp only [up, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def luD (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun h i := (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2
  map_add' h h' := by
    funext i
    simp only [sl_add, up_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Pi.add_apply]
    ring
  map_smul' c h := by
    funext i
    simp only [sl_smul, up_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    ring

def key (e : ι ≃ Fin (Fintype.card ι)) (i : Ix ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.2.1 : ℕ) + i.2.2, toLex ((i.2.1 : ℕ), e i.1))

lemma key_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (key (r := r) e) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : a = a' := Fin.ext h2
  have hb : b = b' := Fin.ext (by omega)
  have hτ : τ = τ' := e.injective h3
  subst ha hb hτ
  rfl

lemma key_le_of (e : ι ≃ Fin (Fintype.card ι)) (τ : ι) {a b a' b' : Fin r} (h1 : (a' : ℕ) + b' ≤ a + b)
    (h2 : (a' : ℕ) ≤ a) : key e (τ, a', b') ≤ key e (τ, a, b) := by
  rw [Prod.Lex.le_iff]
  simp only [key, ofLex_toLex]
  rcases h1.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rcases h2.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', le_rfl⟩

lemma luD_apply (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by
  show (sl h i.1 * up w i.1 + (1 + sl w i.1) * up h i.1) i.2.1 i.2.2 = _
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]

lemma one_add_sl_zero (w : Ix ι r → ℂ) (τ : ι) {a k : Fin r} (h : a < k) : (1 + sl w τ) a k = 0 := by
  rw [Matrix.add_apply, Matrix.one_apply_ne h.ne]
  simp [sl, not_lt.mpr h.le]

lemma toMatrix_luD_zero (e : ι ≃ Fin (Fintype.card ι)) (w : Ix ι r → ℂ) (i j : Ix ι r)
    (hij : key e i < key e j) : LinearMap.toMatrix' (luD w) i j = 0 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hne : ∀ a' b' : Fin r, (a' : ℕ) + b' ≤ a + b → (a' : ℕ) ≤ a → (τ, a', b') ≠ j := by
    rintro a' b' h1 h2 rfl
    exact absurd (key_le_of e τ h1 h2) (not_le.mpr hij)
  have hs1 : ∀ k : Fin r, sl (Pi.single j (1 : ℂ)) τ a k * up w τ k b = 0 := by
    intro k
    by_cases hka : k < a
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne a k (by omega) le_rfl
        simp [Pi.single_apply, sl, hka, this]
    · simp [Pi.single_apply, sl, hka]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single j (1 : ℂ)) τ k b = 0 := by
    intro k
    by_cases hka : a < k
    · rw [one_add_sl_zero w τ hka, zero_mul]
    · by_cases hbk : b < k
      · simp [Pi.single_apply, up, hbk]
      · have := hne k b (by omega) (by omega)
        simp [Pi.single_apply, up, hbk, this]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp

lemma toMatrix_luD_diag (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b =
      if k = b then (if b < a then w (τ, b, b) else 0) else 0 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]
    · simp [Pi.single_apply, sl, hkb]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b =
      if k = a then (if b < a then 0 else 1) else 0 := by
    intro k
    by_cases hka : k = a
    · subst hka
      by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]
    · simp [Pi.single_apply, up, hka]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

theorem det_luD (w : Ix ι r → ℂ) :
    LinearMap.det (luD w) = ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  rw [← LinearMap.det_toMatrix', det_of_key _ (key (r := r) (Fintype.equivFin ι))
    (key_injective _) (fun i j h => toMatrix_luD_zero _ w i j h)]
  exact Finset.prod_congr rfl fun i _ => toMatrix_luD_diag w i

def luD' (w : Ix ι r → ℂ) : (Ix ι r → ℂ) →L[ℝ] (Ix ι r → ℂ) :=
  LinearMap.toContinuousLinearMap ((luD w).restrictScalars ℝ)

lemma hasFDerivAt_entry1 (w : Ix ι r → ℂ) (τ : ι) (a k : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => (1 + sl v τ) a k)
      (if k < a then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, a, k) else 0) w := by
  by_cases hk : k < a
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun v => (1 : Matrix (Fin r) (Fin r) ℂ) a k + v (τ, a, k) := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact (hasFDerivAt_apply (𝕜 := ℝ) (τ, a, k) w).const_add _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => (1 + sl v τ) a k) =
        fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) a k := by
      funext v
      simp [sl, hk]
    rw [hf]
    exact hasFDerivAt_const _ _

lemma hasFDerivAt_entry2 (w : Ix ι r → ℂ) (τ : ι) (k b : Fin r) :
    HasFDerivAt (fun v : Ix ι r → ℂ => up v τ k b)
      (if b < k then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ix ι r => ℂ) (τ, k, b)) w := by
  by_cases hk : b < k
  · rw [if_pos hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun _ => (0 : ℂ) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_const _ _
  · rw [if_neg hk]
    have hf : (fun v : Ix ι r → ℂ => up v τ k b) = fun v => v (τ, k, b) := by
      funext v
      simp [up, hk]
    rw [hf]
    exact hasFDerivAt_apply (𝕜 := ℝ) (τ, k, b) w

theorem hasFDerivAt_lu (w : Ix ι r → ℂ) : HasFDerivAt lu (luD' w) w := by
  rw [hasFDerivAt_pi']
  rintro ⟨τ, a, b⟩
  have hf : (fun v : Ix ι r → ℂ => lu v (τ, a, b)) =
      fun v => ∑ k, (1 + sl v τ) a k * up v τ k b := by
    funext v
    simp only [lu, Matrix.mul_apply]
  rw [hf]
  have hd := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (hasFDerivAt_entry1 w τ a k).mul (hasFDerivAt_entry2 w τ k b))
  convert hd using 1
  · funext v
    simp only [Finset.sum_apply, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply]
    change luD w h (τ, a, b) = _
    rw [luD_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hka : k < a <;> by_cases hbk : b < k <;> simp [hka, hbk, sl, up] <;> ring

theorem det_luD' (w : Ix ι r → ℂ) :
    (luD' w).det = Complex.normSq (∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1) := by
  rw [← det_luD w, ← Algebra.norm_complex_apply]
  show LinearMap.det ((luD w).restrictScalars ℝ) = _
  exact LinearMap.det_restrictScalars

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

noncomputable section

section Mat

variable {n : ℕ}

lemma inv_blockTriangular {α : Type*} [LinearOrder α] {b : Fin n → α} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular b) (hd : M.det ≠ 0) : (M⁻¹).BlockTriangular b := by
  haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

lemma det_lowerUni {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular OrderDual.toDual)
    (h1 : ∀ a, N a a = 1) : N.det = 1 := by
  rw [Matrix.det_of_lowerTriangular N hN]
  simp [h1]

theorem lu_unique {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN1 : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'1 : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id) (hd : U'.det ≠ 0)
    (h : N * U = N' * U') : N = N' ∧ U = U' := by
  first | exact Bl.general_b_fact_form.goal1 .. | (apply Bl.general_b_fact_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_form.goal1 <;> assumption)

lemma lminor_last' (M : Matrix (Fin n) (Fin n) ℂ) : lminor M (Fin.last n) = M.det := by
  rfl

theorem lu_exists {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i : Fin (n + 1), lminor M i ≠ 0) :
    ∃ N U : Matrix (Fin n) (Fin n) ℂ, N.BlockTriangular OrderDual.toDual ∧ (∀ a, N a a = 1) ∧
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ N * U = M := by
  classical
  let A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ := fun r =>
    M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)
  have hA : ∀ r : Fin n, IsUnit (A r).det := fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)
  let x : ∀ r : Fin n, Fin r → ℂ := fun r =>
    -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)
  have hx : ∀ r : Fin n, ∀ j : Fin r,
      ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) =
        -M r (Fin.castLE r.isLt.le j) := by
    intro r j
    have hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j)) := by
      simp only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r),
        Matrix.vecMul_one]
    have h := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, A] using h

  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r c =>
    if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0
  have hLlow : L.BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    simp [L, not_lt.mpr hrc'.le, hrc'.ne']
  have hL1 : ∀ a, L a a = 1 := fun a => by simp [L]
  have hLdet : L.det = 1 := det_lowerUni hLlow hL1
  have hLu : IsUnit L.det := by rw [hLdet]; exact isUnit_one
  have hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0 := by
    intro r c hcr
    have e1 : ∀ k, L r k * M k c =
        (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0) := by
      intro k
      by_cases h : k < r
      · simp [L, h, h.ne]
      · by_cases h' : k = r
        · subst h'
          simp [L]
        · simp [L, h, h']
    have hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) =
        ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castLEEmb r.isLt.le j) < r := by
          show (j : ℕ) < r
          exact j.isLt
        rw [dif_pos hj]
        rfl
      · intro k _ hk
        have hk' : ¬ k < r := by
          intro h
          apply hk
          exact Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [dif_neg hk']
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]
    have h := hx r ⟨c, hcr⟩
    have hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c := Fin.ext rfl
    rw [hc] at h
    rw [h]
    ring
  refine ⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (L * L⁻¹) a a = 1 := by
      rw [Matrix.mul_nonsing_inv L hLu]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rwa [hL1, one_mul] at h1
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · have h0 : L⁻¹ k a = 0 := inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero)
          (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, mul_zero]
      · have h0 : L a k = 0 := hLlow (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro r c hcr
    exact hrow r c hcr
  · rw [Matrix.det_mul, hLdet, one_mul, ← lminor_last']
    exact hM _
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]

end Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def Mt (v : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => v (τ, a, b)

def BC (ι : Type*) [Fintype ι] (r : ℕ) : Set (Ix ι r → ℂ) := {v | ∀ τ, ∀ i : Fin (r + 1), lminor (Mt v τ) i ≠ 0}

def sS (ι : Type*) (r : ℕ) : Set (Ix ι r → ℂ) := {w | ∀ τ b, w (τ, b, b) ≠ 0}

lemma Mt_lu (w : Ix ι r → ℂ) (τ : ι) : Mt (lu w) τ = (1 + sl w τ) * up w τ := by
  ext a b
  rfl

lemma one_add_sl_low (w : Ix ι r → ℂ) (τ : ι) : (1 + sl w τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [sl, Matrix.one_apply_ne hij'.ne, not_lt.mpr hij'.le]

lemma one_add_sl_diag (w : Ix ι r → ℂ) (τ : ι) (a : Fin r) : (1 + sl w τ) a a = 1 := by
  simp [sl]

lemma up_upper (w : Ix ι r → ℂ) (τ : ι) : (up w τ).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  simp [up, hij']

lemma det_up (w : Ix ι r → ℂ) (τ : ι) : (up w τ).det = ∏ b, w (τ, b, b) := by
  rw [Matrix.det_of_upperTriangular (up_upper w τ)]
  simp [up]

lemma det_up_ne {w : Ix ι r → ℂ} (hw : w ∈ sS ι r) (τ : ι) : (up w τ).det ≠ 0 := by
  rw [det_up]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b

lemma eq_of_sl_up {w w' : Ix ι r → ℂ} (h1 : ∀ τ, sl w τ = sl w' τ) (h2 : ∀ τ, up w τ = up w' τ) : w = w' := by
  funext i
  obtain ⟨τ, a, b⟩ := i
  by_cases hba : b < a
  · have h := congrFun (congrFun (h1 τ) a) b
    simpa [sl, hba] using h
  · have h := congrFun (congrFun (h2 τ) a) b
    simpa [up, hba] using h

theorem lu_injOn : Set.InjOn (lu (ι := ι) (r := r)) (sS ι r) := by
  intro w hw w' hw' h
  have key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ := by
    intro τ
    have hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ := by
      rw [← Mt_lu, ← Mt_lu, h]
    exact lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ)
      (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM
  exact eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)

theorem BC_subset_image : BC ι r ⊆ lu '' sS ι r := by
  intro v hv
  choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)
  refine ⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro τ b
    show (if b < b then N τ b b else U τ b b) ≠ 0
    rw [if_neg (lt_irrefl b)]
    intro h0
    have hdet : (U τ).det = ∏ b, U τ b b := Matrix.det_of_upperTriangular (hU τ)
    exact hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)
  · have hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = N τ := by
      intro τ
      ext a b
      rcases lt_trichotomy b a with h | h | h
      · simp [sl, h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h
        simp [sl, hN1]
      · have h0 : N τ a b = 0 := hN τ (OrderDual.toDual_lt_toDual.mpr h)
        simp [sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]
    have hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = U τ := by
      intro τ
      ext a b
      by_cases h : b < a
      · have h0 : U τ a b = 0 := hU τ h
        simp [up, h, h0]
      · simp [up, h]
    funext i
    obtain ⟨τ, a, b⟩ := i
    show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)
    rw [hsl, hup, hNU]
    rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem volume_null_of_slice {I : Type*} [Fintype I] [DecidableEq I] (i0 : I) {S : Set (I → ℂ)}
    (hS : MeasurableSet S) (huniq : ∀ v ∈ S, ∀ v' ∈ S, (∀ j, j ≠ i0 → v j = v' j) → v = v') :
    volume S = 0 := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℂ) (fun j => j ≠ i0)
  have hmp : MeasurePreserving e (volume : Measure (I → ℂ))
      ((Measure.pi fun _ : {j // j ≠ i0} => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure ℂ)) (fun j => j ≠ i0)
  have hS' : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hS
  rw [← hmp.symm.measure_preimage_equiv S, Measure.measure_prod_null hS']
  refine Filter.Eventually.of_forall fun x => ?_
  haveI : Nonempty {j // ¬ j ≠ i0} := ⟨⟨i0, not_not.2 rfl⟩⟩
  show (Measure.pi fun _ : {j // ¬ j ≠ i0} => (volume : Measure ℂ)) _ = 0
  refine Set.Subsingleton.measure_zero ?_ _
  intro y hy y' hy'
  have hxy : e.symm (x, y) = e.symm (x, y') := by
    refine huniq _ hy _ hy' fun j hj => ?_
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have := e.symm.injective hxy
  exact (Prod.ext_iff.1 this).2

lemma det_diff_last {k : ℕ} (B B' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ∀ a b, ¬ (a = Fin.last k ∧ b = Fin.last k) → B a b = B' a b) :
    B.det - B'.det = (B (Fin.last k) (Fin.last k) - B' (Fin.last k) (Fin.last k)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  have hrows : ∀ j : Fin (k + 1), B.submatrix (Fin.last k).succAbove j.succAbove =
      B'.submatrix (Fin.last k).succAbove j.succAbove := by
    intro j
    ext a b
    refine h _ _ fun hab => ?_
    have := hab.1
    rw [Fin.succAbove_last] at this
    exact Fin.castSucc_ne_last a this
  rw [Matrix.det_succ_row B (Fin.last k), Matrix.det_succ_row B' (Fin.last k),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single (Fin.last k)]
  · rw [hrows (Fin.last k)]
    have hs : (-1 : ℂ) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]; simp
    have hc : B.submatrix Fin.castSucc Fin.castSucc = B'.submatrix Fin.castSucc Fin.castSucc := by
      simpa [Fin.succAbove_last] using hrows (Fin.last k)
    rw [hs, Fin.succAbove_last, hc]
    ring
  · intro j _ hj
    have hrow : B (Fin.last k) j = B' (Fin.last k) j := h _ _ fun hab => hj hab.2
    rw [hrow, hrows j]
    ring
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma continuous_lminor (τ : ι) (i : Fin (r + 1)) : Continuous fun v : Ix ι r → ℂ => lminor (Mt v τ) i := by
  unfold Mt lminor
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_apply _

theorem volume_lminor_zero (τ : ι) :
    ∀ k (h : k < r + 1), volume {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, h⟩ = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro h
    have hempty : {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨0, h⟩ = 0} = ∅ := by
      ext v
      simp [lminor]
    rw [hempty, measure_empty]
  | succ k ih =>
    intro h
    have hk : k < r + 1 := by omega
    have hkr : k < r := by omega
    have hl : (Fin.castLE (Nat.le_of_lt_succ h) (Fin.last k) : Fin r) = ⟨k, hkr⟩ :=
      Fin.ext (by simp)
    have key : ∀ w : Ix ι r → ℂ, lminor (Mt w τ) ⟨k, hk⟩ =
        (((Mt w τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h))).submatrix
          Fin.castSucc Fin.castSucc).det := fun w => rfl
    have hmeas : MeasurableSet {v : Ix ι r → ℂ |
        lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0} :=
      (isClosed_eq (continuous_lminor τ _) continuous_const).measurableSet.inter
        (isClosed_eq (continuous_lminor τ _) continuous_const).isOpen_compl.measurableSet
    refine measure_mono_null (t := {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k, hk⟩ = 0} ∪
      {v : Ix ι r → ℂ | lminor (Mt v τ) ⟨k + 1, h⟩ = 0 ∧ lminor (Mt v τ) ⟨k, hk⟩ ≠ 0}) ?_ ?_
    · intro v hv
      by_cases h0 : lminor (Mt v τ) ⟨k, hk⟩ = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hv, h0⟩
    refine measure_union_null (ih hk) ?_
    refine volume_null_of_slice (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) hmeas ?_
    intro v hv v' hv' hagree
    have dd := det_diff_last
      ((Mt v τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      ((Mt v' τ).submatrix (Fin.castLE (Nat.le_of_lt_succ h)) (Fin.castLE (Nat.le_of_lt_succ h)))
      (by
        intro a b hab
        refine hagree _ fun heq => hab ?_
        simp only [Prod.mk.injEq, Fin.ext_iff, Fin.coe_castLE] at heq
        exact ⟨Fin.ext (by simp [heq.2.1]), Fin.ext (by simp [heq.2.2])⟩)
    have h1 : lminor (Mt v τ) ⟨k + 1, h⟩ = 0 := hv.1
    have h2 : lminor (Mt v' τ) ⟨k + 1, h⟩ = 0 := hv'.1
    have hm : lminor (Mt v τ) ⟨k, hk⟩ ≠ 0 := hv.2
    rw [key v] at hm
    simp only [lminor] at h1 h2
    rw [h1, h2, sub_zero] at dd
    simp only [Matrix.submatrix_apply, hl] at dd
    have hz : v (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) - v' (τ, ⟨k, hkr⟩, ⟨k, hkr⟩) = 0 := by
      rcases mul_eq_zero.1 dd.symm with hz | hz
      · exact hz
      · exact absurd hz hm
    funext j
    by_cases hj : j = (τ, ⟨k, hkr⟩, ⟨k, hkr⟩)
    · subst hj; exact sub_eq_zero.1 hz
    · exact hagree j hj

theorem volume_BC_compl : volume (BC ι r)ᶜ = 0 := by
  have hU : (BC ι r)ᶜ = ⋃ τ : ι, ⋃ i : Fin (r + 1), {v : Ix ι r → ℂ | lminor (Mt v τ) i = 0} := by
    ext v
    simp [BC]
  rw [hU]
  refine measure_iUnion_null fun τ => measure_iUnion_null fun i => ?_
  exact volume_lminor_zero τ i.1 i.2

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev UpI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // ¬ i.2.2 < i.2.1}

abbrev LoI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // i.2.2 < i.2.1}

def Umat (y : UpI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : ¬ b < a then y ⟨(τ, a, b), h⟩ else 0

lemma Umat_add (y y' : UpI ι r → ℂ) (τ : ι) : Umat (y + y') τ = Umat y τ + Umat y' τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma Umat_smul (c : ℂ) (y : UpI ι r → ℂ) (τ : ι) : Umat (c • y) τ = c • Umat y τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : (UpI ι r → ℂ) →ₗ[ℂ] (UpI ι r → ℂ) where
  toFun y i := (β i.1.1 * Umat y i.1.1) i.1.2.1 i.1.2.2
  map_add' y y' := by funext i; simp [Umat_add, Matrix.mul_add]
  map_smul' c y := by funext i; simp [Umat_smul]

def keyU (e : ι ≃ Fin (Fintype.card ι)) (i : UpI ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.1.2.2 : ℕ), toLex (r - (i.1.2.1 : ℕ), e i.1.1))

lemma keyU_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩

private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp

lemma toMatrix_Lβ_zero (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl

lemma toMatrix_Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (i : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i i = β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [toMatrix_entry_lemma, if_pos ⟨rfl, rfl⟩]

theorem det_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def dI (τ : ι) (b : Fin r) : UpI ι r := ⟨(τ, b, b), lt_irrefl b⟩

def jacU (y : UpI ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then y (dI i.1 i.2.2) else 1

def jacβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then β i.1 i.2.2 i.2.2 else 1

def Cy (ι : Type*) [Fintype ι] (r : ℕ) : Set (UpI ι r → ℂ) :=
  {y | ∀ i : UpI ι r, (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧ (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)}

def K0 (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) : ENNReal :=
  ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y))

lemma Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ)
    (τ : ι) (b : Fin r) : Lβ β y (dI τ b) = β τ b b * y (dI τ b) := by
  show (β τ * Umat y τ) b b = β τ b b * y (dI τ b)
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp [Umat, dI]
  · intro c _ hcb
    rcases lt_or_gt_of_ne hcb with h | h
    · rw [hβ τ h, zero_mul]
    · simp [Umat, h]
  · intro h
    exact absurd (Finset.mem_univ b) h

lemma jacU_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ) :
    jacU (Lβ β y) = jacβ β * jacU y := by
  unfold jacU jacβ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact Lβ_diag β hβ y i.1 i.2.2
  · simp

lemma measurableSet_Cy : MeasurableSet (Cy ι r) := by
  have h : Cy ι r = ⋂ i : UpI ι r, {y : UpI ι r → ℂ | (i.1.2.1 = i.1.2.2 → 1 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 2) ∧
      (i.1.2.1 ≠ i.1.2.2 → ‖y i‖ ≤ 1)} := by
    ext y
    simp [Cy]
  refine IsClosed.measurableSet ?_
  rw [h]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun y : UpI ι r → ℂ => ‖y i‖ := (continuous_apply i).norm
  by_cases hi : i.1.2.1 = i.1.2.2
  · simp only [hi, ne_eq, not_true_eq_false, false_implies, and_true, true_implies]
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  · simp only [hi, ne_eq, not_false_eq_true, true_implies, false_implies, true_and]
    exact isClosed_le hc continuous_const

lemma norm_le_of_Cy {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) (i : UpI ι r) : ‖y i‖ ≤ 2 := by
  by_cases hi : i.1.2.1 = i.1.2.2
  · exact ((hy i).1 hi).2
  · exact ((hy i).2 hi).trans (by norm_num)

lemma one_le_normSq_jacU {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) : 1 ≤ Complex.normSq (jacU y) := by
  unfold jacU
  rw [map_prod]
  calc (1 : ℝ) = ∏ _i : Ix ι r, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => ?_
      split_ifs
      · have h1 := ((hy (dI i.1 i.2.2)).1 rfl).1
        rw [Complex.normSq_eq_norm_sq]
        nlinarith
      · simp

lemma normSq_jacU_le {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) :
    Complex.normSq (jacU y) ≤ 4 ^ Fintype.card (Ix ι r) := by
  unfold jacU
  rw [map_prod]
  calc _ ≤ ∏ _i : Ix ι r, (4 : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => Complex.normSq_nonneg _) fun i _ => ?_
        split_ifs
        · have h1 := norm_le_of_Cy hy (dI i.1 i.2.2)
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg (y (dI i.1 i.2.2))]
        · simp
    _ = 4 ^ Fintype.card (Ix ι r) := by rw [Finset.prod_const, Finset.card_univ]

lemma Cy_subset_ball : Cy ι r ⊆ Metric.closedBall 0 2 := fun y hy =>
  mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => norm_le_of_Cy hy i)

lemma continuous_jacU : Continuous (jacU (ι := ι) (r := r)) := by
  unfold jacU
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases h : i.2.2 < i.2.1
  · simp only [h, ↓reduceIte]
    exact continuous_apply _
  · simp only [h, ↓reduceIte]
    exact continuous_const

lemma measurable_normSq_jacU : Measurable fun y : UpI ι r → ℂ => ENNReal.ofReal (Complex.normSq (jacU y)) :=
  (ENNReal.continuous_ofReal.comp (Complex.continuous_normSq.comp continuous_jacU)).measurable

lemma measureConstant_lt_top : K0 ι r < ⊤ := by
  unfold K0
  calc ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y))
      ≤ ∫⁻ _y in Cy ι r, ENNReal.ofReal (4 ^ Fintype.card (Ix ι r)) :=
        setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal (normSq_jacU_le hy)
    _ = ENNReal.ofReal (4 ^ Fintype.card (Ix ι r)) * volume (Cy ι r) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((measure_mono Cy_subset_ball).trans_lt measure_closedBall_lt_top)

lemma ball_subset_Cy : Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2) ⊆ Cy ι r := by
  intro y hy i
  have h := (dist_le_pi_dist y (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) i).trans_lt
    (Metric.mem_ball.1 hy)
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  constructor
  · intro hi
    simp only [hi, ↓reduceIte, Complex.dist_eq] at h
    have h1 := norm_sub_norm_le (y i) (3 / 2)
    have h2 := norm_sub_norm_le (3 / 2 : ℂ) (y i)
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  · intro hi
    simp only [hi, ↓reduceIte, dist_zero_right] at h
    linarith

lemma finrank_maxUnramifiedSubfield_padicFinExt_pos : 0 < K0 ι r := by
  unfold K0
  calc (0 : ENNReal)
      < volume (Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2)) :=
        Metric.measure_ball_pos _ _ (by norm_num)
    _ ≤ volume (Cy ι r) := measure_mono ball_subset_Cy
    _ = ∫⁻ _y in Cy ι r, 1 := (setLIntegral_one _).symm
    _ ≤ ∫⁻ y in Cy ι r, ENNReal.ofReal (Complex.normSq (jacU y)) :=
        setLIntegral_mono measurable_normSq_jacU fun y hy => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_normSq_jacU hy)

lemma det_Lβ_ne (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) : LinearMap.det (Lβ β) ≠ 0 := by
  rw [det_Lβ β hβ]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd _ _

lemma jacβ_ne (β : ι → Matrix (Fin r) (Fin r) ℂ) (hd : ∀ τ b, β τ b b ≠ 0) : jacβ β ≠ 0 := by
  unfold jacβ
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs
  · exact hd _ _
  · exact one_ne_zero

theorem lintegral_upper (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
  set LR : (UpI ι r → ℂ) →ₗ[ℝ] (UpI ι r → ℂ) := (Lβ β).restrictScalars ℝ with hLR_def
  have hdet : LinearMap.det LR = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [hLR_def, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdn := det_Lβ_ne β hβ hd
  have hdR : LinearMap.det LR ≠ 0 := by
    rw [hdet]
    exact (Complex.normSq_pos.2 hdn).ne'
  have hjbp : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 (jacβ_ne β hd)
  set G : (UpI ι r → ℂ) → ENNReal := fun z =>
    ENNReal.ofReal (Complex.normSq (jacU z) / Complex.normSq (jacβ β)) * (Cy ι r).indicator 1 z with hG_def
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp
      ((Complex.continuous_normSq.comp continuous_jacU).measurable.div_const _)).mul
      (measurable_one.indicator measurableSet_Cy)
  have hLRm : Measurable LR := LR.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy ι r).indicator 1 (Lβ β y) = G (LR y) := by
    intro y
    have e : LR y = Lβ β y := rfl
    rw [hG_def]
    dsimp only
    rw [e, jacU_Lβ β hβ, map_mul, mul_div_cancel_left₀ _ hjbp.ne']
  have hint : ∫⁻ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) * K0 ι r := by
    have e : ∀ z, G z = ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹) *
        (Cy ι r).indicator (fun z => ENNReal.ofReal (Complex.normSq (jacU z))) z := by
      intro z
      rw [hG_def]
      dsimp only
      by_cases hz : z ∈ Cy ι r
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, mul_one, div_eq_mul_inv,
          ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]
    rw [lintegral_congr e, lintegral_const_mul _ (measurable_normSq_jacU.indicator measurableSet_Cy),
      lintegral_indicator measurableSet_Cy]
    rfl
  rw [lintegral_congr hpt, ← lintegral_map hG hLRm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdR,
    lintegral_smul_measure, hint, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hdet,
    abs_of_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)), ← mul_inv]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def jac (w : Ix ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1

lemma continuous_lu : Continuous (lu (ι := ι) (r := r)) := by
  have hsl : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => sl w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [sl, h] <;> fun_prop
  have hup : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => up w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [up, h] <;> fun_prop
  refine continuous_pi fun i => ?_
  simp only [lu, Matrix.mul_apply, Matrix.add_apply]
  exact continuous_finset_sum _ fun k _ => (continuous_const.add (hsl _ _ _)).mul (hup _ _ _)

lemma continuous_jac : Continuous (jac (ι := ι) (r := r)) := by
  unfold jac
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h] <;> fun_prop

lemma measurableSet_sS : MeasurableSet (sS ι r) := by
  unfold sS
  have h : {w : Ix ι r → ℂ | ∀ (τ : ι) (b : Fin r), w (τ, b, b) ≠ 0} =
      ⋂ τ : ι, ⋂ b : Fin r, (fun w : Ix ι r → ℂ => w (τ, b, b)) ⁻¹' {0}ᶜ := by
    ext w
    simp
  rw [h]
  exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b =>
    measurable_pi_apply _ (measurableSet_singleton 0).compl

theorem lintegral_lu (g : (Ix ι r → ℂ) → ENNReal) :
    ∫⁻ v, g v = ∫⁻ w in sS ι r, ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w) := by
  have hae : ∀ᵐ v ∂(volume : Measure (Ix ι r → ℂ)), v ∈ lu '' sS ι r := by
    refine measure_mono_null (fun v hv => ?_) (volume_BC_compl (ι := ι) (r := r))
    exact fun hB => hv (BC_subset_image (ι := ι) (r := r) hB)
  rw [show ∫⁻ v, g v = ∫⁻ v in lu '' sS ι r, g v by rw [Measure.restrict_eq_self_of_ae_mem hae],
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_sS
      (fun w _ => (hasFDerivAt_lu w).hasFDerivWithinAt) lu_injOn g]
  refine setLIntegral_congr_fun (measurableSet_sS (ι := ι) (r := r)) (fun w _ => ?_)
  rw [det_luD', abs_of_nonneg (Complex.normSq_nonneg _)]
  rfl

def eS (ι : Type*) [Fintype ι] (r : ℕ) : (Ix ι r → ℂ) ≃ᵐ (LoI ι r → ℂ) × (UpI ι r → ℂ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)

lemma eS_symm_apply (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (i : Ix ι r) :
    (eS ι r).symm (x, y) i = if h : i.2.2 < i.2.1 then x ⟨i, h⟩ else y ⟨i, h⟩ := rfl

def Nmat (x : LoI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : b < a then x ⟨(τ, a, b), h⟩ else if a = b then 1 else 0



lemma jac_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) : jac ((eS ι r).symm (x, y)) = jacU y := by
  unfold jac jacU
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h, eS_symm_apply, dI]

lemma mem_sS_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) :
    (eS ι r).symm (x, y) ∈ sS ι r ↔ ∀ τ b, y (dI τ b) ≠ 0 := by
  simp [sS, eS_symm_apply, dI]


theorem lintegral_flat {g : (Ix ι r → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v = ∫⁻ x, ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * g (lu ((eS ι r).symm (x, y))) else 0) := by
  have hmp : MeasurePreserving (eS ι r) volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)
  set F : (Ix ι r → ℂ) → ENNReal :=
    (sS ι r).indicator (fun w => ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w)) with hF
  have hFm : Measurable F :=
    ((Complex.continuous_normSq.comp continuous_jac).measurable.ennreal_ofReal.mul
      (hg.comp continuous_lu.measurable)).indicator measurableSet_sS
  rw [lintegral_lu]
  first
  | rw [← lintegral_indicator measurableSet_sS]
  | rw [← lintegral_indicator _ measurableSet_sS]
  rw [← hmp.symm.lintegral_comp_emb (eS ι r).symm.measurableEmbedding, Measure.volume_eq_prod]
  refine (lintegral_prod _ ?_).trans ?_
  · exact (hFm.comp (eS ι r).symm.measurable).aemeasurable
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  by_cases h : ∀ τ b, y (dI τ b) ≠ 0
  · rw [if_pos h, Set.indicator_of_mem ((mem_sS_eS x y).2 h)]
    simp only [jac_eS]
  · rw [if_neg h]
    first
    | exact Set.indicator_of_notMem (fun hm => h ((mem_sS_eS x y).1 hm)) _
    | exact Set.indicator_of_not_mem (fun hm => h ((mem_sS_eS x y).1 hm)) _
end
end MI
end Up
end AR
end G
end ChartRestriction
end ReciprocityTheory
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def LA (A : ι → Matrix (Fin r) (Fin r) ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun v i := (A i.1 * Mt v i.1) i.2.1 i.2.2
  map_add' v v' := by
    funext i; simp only [Pi.add_apply, Matrix.mul_apply, Mt, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i; simp only [Pi.smul_apply, Matrix.mul_apply, Mt, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

def eB (ι : Type*) (r : ℕ) : Ix ι r ≃ Fin r × (ι × Fin r) where
  toFun i := (i.2.1, (i.1, i.2.2))
  invFun j := (j.2.1, j.1, j.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.det (LA A) = ∏ τ, (A τ).det ^ r := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ix ι r)), ← Matrix.det_reindex_self (eB ι r)]
  have hM : Matrix.reindex (eB ι r) (eB ι r)
      (LinearMap.toMatrix (Pi.basisFun ℂ (Ix ι r)) (Pi.basisFun ℂ (Ix ι r)) (LA A)) =
      Matrix.blockDiagonal (fun k : ι × Fin r => A k.1) := by
    ext ⟨a, τ, b⟩ ⟨c, τ', d⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.blockDiagonal_apply]
    simp only [eB, Equiv.coe_fn_symm_mk, LA, LinearMap.coe_mk, AddHom.coe_mk, Mt, Matrix.mul_apply,
      Matrix.of_apply]
    by_cases h : (τ, b) = (τ', d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [if_pos rfl, Finset.sum_eq_single c]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ((τ, k, b) : Ix ι r) ≠ (τ', c, d) := by
        intro he
        apply h
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩
      simp [Pi.single_apply, this]
  rw [hM, Matrix.det_blockDiagonal, Fintype.prod_prod_type]
  simp [Finset.prod_const]

theorem lintegral_comp_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ τ, (A τ).det ≠ 0)
    {F : (Ix ι r → ℂ) → ENNReal} (hF : Measurable F) :
    ∫⁻ v, F (LA A v) = ENNReal.ofReal (Complex.normSq (∏ τ, (A τ).det ^ r))⁻¹ * ∫⁻ v, F v := by
  have hdet : LinearMap.det ((LA A).restrictScalars ℝ) = Complex.normSq (∏ τ, (A τ).det ^ r) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_LA]
  have hne : LinearMap.det ((LA A).restrictScalars ℝ) ≠ 0 := by
    rw [hdet, Ne, Complex.normSq_eq_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hA τ)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Ix ι r → ℂ))) hne
  have hmeas : Measurable ((LA A).restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ v, F (LA A v) = ∫⁻ v, F ((LA A).restrictScalars ℝ v) := rfl
    _ = ∫⁻ v, F v ∂(Measure.map ((LA A).restrictScalars ℝ) volume) :=
        (lintegral_map hF hmeas).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, hdet,
          abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)), smul_eq_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

private lemma blockTriangular_inv_of_det_ne_zero {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.BlockTriangular id)
    (hd : M.det ≠ 0) : M⁻¹.BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

private lemma eq_of_mul_mul_eq_of_det_ne_zero {P Q X Y : Matrix (Fin n) (Fin n) ℂ} (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  have hP' := isUnit_iff_ne_zero.mpr hP
  have hQ' := isUnit_iff_ne_zero.mpr hQ
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = P⁻¹ * (P * Z * Q) * Q⁻¹ := by
    intro Z
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP', Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
  calc X = P⁻¹ * (P * X * Q) * Q⁻¹ := e X
    _ = P⁻¹ * (P * Y * Q) * Q⁻¹ := by rw [h]
    _ = Y := (e Y).symm

theorem gram_upper_unique {ε : Fin n → ℂ} (hε : ∀ a, ε a * ε a = 1)
    {β β' : Matrix (Fin n) (Fin n) ℂ} (hβ : β.BlockTriangular id) (hβ' : β'.BlockTriangular id)
    (hd : β.det ≠ 0) (hd' : β'.det ≠ 0)
    (h : β'ᵀ * diagonal ε * β'.map (starRingEnd ℂ) = βᵀ * diagonal ε * β.map (starRingEnd ℂ)) :
    ∃ D : Fin n → ℂ, (∀ a, ‖D a‖ = 1) ∧ β' = diagonal D * β := by
  classical
  have hε0 : ∀ a, ε a ≠ 0 := fun a h0 => by
    have := hε a
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hu := isUnit_iff_ne_zero.mpr hd
  obtain ⟨γ, hγdef⟩ : ∃ γ : Matrix (Fin n) (Fin n) ℂ, γ = β' * β⁻¹ := ⟨_, rfl⟩
  have hγ : γ.BlockTriangular id := hγdef ▸ hβ'.mul (blockTriangular_inv_of_det_ne_zero hβ hd)
  have hγβ : β' = γ * β := by
    rw [hγdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hγd : γ.det ≠ 0 := by
    intro h0
    apply hd'
    rw [hγβ, Matrix.det_mul, h0, zero_mul]
  have hbar : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => by
    rw [RingHom.map_det]; rfl

  have key : γᵀ * diagonal ε * γ.map (starRingEnd ℂ) = diagonal ε := by
    apply eq_of_mul_mul_eq_of_det_ne_zero (P := βᵀ) (Q := β.map (starRingEnd ℂ))
    · rwa [Matrix.det_transpose]
    · rw [hbar]; exact (map_ne_zero _).mpr hd
    · rw [← h, hγβ, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
  have hγinv := blockTriangular_inv_of_det_ne_zero hγ hγd
  have hγtu : IsUnit γᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hγd

  have key2 : diagonal ε * γ.map (starRingEnd ℂ) = (γ⁻¹)ᵀ * diagonal ε := by
    rw [Matrix.transpose_nonsing_inv]
    conv_rhs => rw [← key]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγtu, Matrix.one_mul]
  have hoff : ∀ i j, i ≠ j → γ i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have e := congrFun (congrFun key2 i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hγinv hlt, zero_mul,
        Matrix.map_apply] at e
      exact (map_eq_zero _).mp ((mul_eq_zero.mp e).resolve_left (hε0 i))
    · exact hγ hlt
  have hγdiag : γ = diagonal (fun a => γ a a) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun a => γ a a, fun a => ?_, by rw [← hγdiag]; exact hγβ⟩
  have e := congrFun (congrFun key a) a
  rw [hγdiag] at e
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at e
  have h2 : γ a a * starRingEnd ℂ (γ a a) = 1 := by
    have : ε a * (γ a a * starRingEnd ℂ (γ a a)) = ε a * 1 := by linear_combination e
    exact mul_left_cancel₀ (hε0 a) this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖γ a a‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Jd : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def gramT (β : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ := βᵀ * Jd X * β.map (starRingEnd ℂ)

def CmatSet : Set (Frame X.Ψ r) :=
  {β | ∀ τ a b, (b < a → β τ a b = 0) ∧ (a = b → 1 ≤ ‖β τ a b‖ ∧ ‖β τ a b‖ ≤ 2) ∧ (a < b → ‖β τ a b‖ ≤ 1)}

def SW : Set (Frame X.Ψ r) :=
  {y | y ∈ X.dom ∧ ∃ β ∈ CmatSet X, ∀ τ, gram τ.1 X.Gm (mat y τ) = gramT X (mat β τ)}

def Wf (y : Frame X.Ψ r) : ENNReal := (SW X).indicator 1 y

def uf (v : Ix X.Ψ r → ℂ) : Frame X.Ψ r := fun τ a b => v (τ, a, b)

lemma sgn_mul_self (p0 a : ℕ) : ((sgn p0 a : ℝ) : ℂ) * ((sgn p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> norm_num

lemma CmatSet_diag_smul {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) {D : X.Ψ → Fin r → ℂ}
    (hD : ∀ τ a, ‖D τ a‖ = 1) : (fun τ => (diagonal (D τ) * mat β τ : Matrix (Fin r) (Fin r) ℂ)) ∈ CmatSet X := by
  simp only [CmatSet, Set.mem_setOf_eq] at hβ ⊢
  intro τ a b
  obtain ⟨h1, h2, h3⟩ := hβ τ a b
  simp only [Matrix.diagonal_mul, mat, Matrix.of_apply, norm_mul, hD, one_mul]
  exact ⟨fun h => by rw [h1 h, mul_zero], h2, h3⟩

lemma CmatSet_upper {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) (τ : X.Ψ) :
    (mat β τ).BlockTriangular id := fun a b h => (hβ τ a b).1 h

lemma CmatSet_det {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) (τ : X.Ψ) : (mat β τ).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular (CmatSet_upper X hβ τ)]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  intro h0
  have h1 := ((hβ τ a a).2.1 rfl).1
  have h0' : β τ a a = 0 := h0
  rw [h0', norm_zero] at h1
  norm_num at h1

lemma mem_CmatSet_iff_Cy (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (y : UpI X.Ψ r → ℂ) :
    (fun τ => (β τ * Umat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ CmatSet X ↔ Lβ β y ∈ Cy X.Ψ r := by
  have hU : ∀ τ, (Umat y τ).BlockTriangular id := by
    intro τ a b h
    have h' : b < a := h
    simp only [Umat, Matrix.of_apply]
    rw [dif_neg (not_not.2 h')]
  have hP : ∀ τ, (β τ * Umat y τ).BlockTriangular id := fun τ => (hβ τ).mul (hU τ)
  simp only [Cy, CmatSet, Set.mem_setOf_eq]
  constructor
  · intro h i
    obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨_, h2, h3⟩ := h τ a b
    exact ⟨fun hab => h2 hab, fun hab => h3 (lt_of_le_of_ne (not_lt.1 hi) hab)⟩
  · intro h τ a b
    refine ⟨fun hab => hP τ hab, fun hab => ?_, fun hab => ?_⟩
    · subst hab
      exact (h ⟨(τ, a, a), lt_irrefl a⟩).1 rfl
    · exact (h ⟨(τ, a, b), not_lt.2 hab.le⟩).2 (ne_of_lt hab)

def UF (y : UpI X.Ψ r → ℂ) : Frame X.Ψ r := fun τ => Umat y τ

def β0 (y : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat (bOf X y) τ)⁻¹

lemma bOf_det {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (mat (bOf X y) τ).det ≠ 0 := by
  have h := bOf_mem (X := X) hy
  simp only [Bor, Set.mem_setOf_eq] at h
  exact (h τ).1

lemma β0_upper {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).BlockTriangular id := by
  have h := bOf_mem (X := X) hy
  simp only [Bor, Set.mem_setOf_eq] at h
  have hu : (mat (bOf X y) τ).BlockTriangular id := fun a c hac => (h τ).2 a c hac
  letI := (mat (bOf X y) τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

lemma β0_det {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).det ≠ 0 := by
  intro h0
  have h1 := Matrix.det_mul (mat (bOf X y) τ) (mat (bOf X y) τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ)), Matrix.det_one] at h1
  have h0' : ((mat (bOf X y) τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1

lemma gram_rmul_eq {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (rmul y b) τ) = gramT X (β0 X y τ * mat b τ) := by
  have hB := bOf_det X hy τ
  have hyB : gram τ.1 X.Gm (mat y τ * mat (bOf X y) τ) = Jd X := ortho_bOf (X := X) hy τ
  have hy' : mat y τ = mat y τ * mat (bOf X y) τ * (mat (bOf X y) τ)⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hB), Matrix.mul_one]
  have hgy : gram τ.1 X.Gm (mat y τ) = (β0 X y τ)ᵀ * Jd X * (β0 X y τ).map (starRingEnd ℂ) := by
    rw [hy', gram_mul, hyB]
    rfl
  show gram τ.1 X.Gm (mat y τ * mat b τ) = _
  rw [gram_mul, hgy]
  unfold gramT
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

lemma UF_mem {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) : UF X y ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  have hU : (Umat y τ).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp only [Umat, Matrix.of_apply]
    rw [dif_neg (not_not.2 h')]
  refine ⟨?_, fun a c h => hU h⟩
  show (Umat y τ).det ≠ 0
  rw [Matrix.det_of_upperTriangular hU]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have e : Umat y τ a a = y (dI τ a) := by
    unfold Umat dI
    rw [Matrix.of_apply, dif_pos (lt_irrefl a)]
  rw [e]
  exact hy τ a

private lemma mem_dom_rmul {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul y b ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hy ⊢
  simp only [Bor, Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, hpos⟩ := hy τ
  obtain ⟨hbdet, hbup⟩ := hb τ
  have hup : (mat b τ).BlockTriangular id := fun a c h => hbup a c h
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h := hbdet
    rw [Matrix.det_of_upperTriangular hup] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  refine ⟨?_, fun i => ?_⟩
  · show (mat y τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hbdet
  · have hb2 : b ∈ Bor X.Ψ r := fun τ' => hb τ'
    rw [dmin_rmul (X := X) y hb2 τ i]
    set p := ∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) with hp
    have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have e : p * dmin X.Gm y τ i * conj p = (Complex.normSq p : ℂ) * dmin X.Gm y τ i := by
      rw [← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq p := Complex.normSq_pos.2 hp0
    have h3 := hpos i
    nlinarith

theorem Wf_rmul_UF {y : Frame X.Ψ r} (hy : y ∈ X.dom) {y' : UpI X.Ψ r → ℂ} (hy' : ∀ τ b, y' (dI τ b) ≠ 0) :
    Wf X (rmul y (UF X y')) = (Cy X.Ψ r).indicator 1 (Lβ (β0 X y) y') := by
  have hb := UF_mem X hy'
  have hdom : rmul y (UF X y') ∈ X.dom := mem_dom_rmul X hy hb
  have hb' := hb
  simp only [Bor, Set.mem_setOf_eq] at hb'
  have hβu : ∀ τ, (β0 X y τ).BlockTriangular id := fun τ => β0_upper X hy τ
  have key : rmul y (UF X y') ∈ SW X ↔ Lβ (β0 X y) y' ∈ Cy X.Ψ r := by
    rw [← mem_CmatSet_iff_Cy X (β0 X y) hβu y']
    constructor
    · rintro ⟨-, β, hβ, hg⟩
      have hU : ∀ τ, (mat (UF X y') τ).BlockTriangular id := fun τ a c h => (hb' τ).2 a c h
      have hD : ∀ τ, ∃ D : Fin r → ℂ, (∀ a, ‖D a‖ = 1) ∧
          mat β τ = diagonal D * (β0 X y τ * mat (UF X y') τ) := by
        intro τ
        refine gram_upper_unique (ε := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => sgn_mul_self X.p0 a)
          ((hβu τ).mul (hU τ)) (CmatSet_upper X hβ τ) ?_ (CmatSet_det X hβ τ) ?_
        · rw [Matrix.det_mul]
          exact mul_ne_zero (β0_det X hy τ) (hb' τ).1
        · exact (hg τ).symm.trans (gram_rmul_eq X hy τ)
      choose D hD1 hD2 using hD
      have e : (fun τ => (β0 X y τ * Umat y' τ : Matrix (Fin r) (Fin r) ℂ)) =
          fun τ => (diagonal (fun a => conj (D τ a)) * mat β τ : Matrix (Fin r) (Fin r) ℂ) := by
        funext τ
        have h1 : (fun a => conj (D τ a) * D τ a) = fun _ => (1 : ℂ) := by
          funext a
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hD1 τ a]
          norm_num
        rw [hD2 τ, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h1, Matrix.diagonal_one, Matrix.one_mul]
        rfl
      rw [e]
      exact CmatSet_diag_smul X (D := fun τ a => conj (D τ a)) hβ (fun τ a => by simpa using hD1 τ a)
    · intro h
      exact ⟨hdom, fun τ => (β0 X y τ * Umat y' τ : Matrix (Fin r) (Fin r) ℂ), h, fun τ => gram_rmul_eq X hy τ⟩
  unfold Wf
  by_cases h : Lβ (β0 X y) y' ∈ Cy X.Ψ r
  · have h2 := key.2 h
    simp [Set.indicator_apply, h, h2]
  · have h2 : rmul y (UF X y') ∉ SW X := fun h' => h (key.1 h')
    simp [Set.indicator_apply, h, h2]

def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

lemma invF_mem' {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hd, hup⟩ := hb τ
  have hu : (mat b τ).BlockTriangular id := fun a c h => hup a c h
  letI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hu
  refine ⟨?_, fun a c h => hinv h⟩
  intro h0
  have h1 := Matrix.det_mul (mat b τ) (mat b τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.det_one] at h1
  have h0' : ((mat b τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1

lemma rmul_invF {y b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul (rmul y b) (invF X b) = y := by
  have hb' := hb
  simp only [Bor, Set.mem_setOf_eq] at hb'
  funext τ
  have hd := (hb' τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.mul_one]
  rfl

theorem Wf_rmul_not_dom {y b : Frame X.Ψ r} (hy : y ∉ X.dom) (hb : b ∈ Bor X.Ψ r) : Wf X (rmul y b) = 0 := by
  unfold Wf
  have h : rmul y b ∉ SW X := by
    rintro ⟨h1, -⟩
    apply hy
    have h2 := mem_dom_rmul X h1 (invF_mem' X hb)
    rwa [rmul_invF X hb] at h2
  simp [Set.indicator_apply, h]

lemma isClosed_imp {P : Prop} {S : Set ℂ} (hS : IsClosed S) : IsClosed {z : ℂ | P → z ∈ S} := by
  by_cases h : P
  · simpa [h] using hS
  · simp [h]

lemma continuous_coord (τ : X.Ψ) (a b : Fin r) : Continuous fun β : Frame X.Ψ r => β τ a b := (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

lemma isCompact_CmatSet : IsCompact (CmatSet X) := by
  have hS : ∀ a b : Fin r, IsCompact {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    intro a b
    apply Metric.isCompact_of_isClosed_isBounded
    · rw [Set.setOf_and, Set.setOf_and]
      refine IsClosed.inter (isClosed_imp (S := {0}) isClosed_singleton)
        (IsClosed.inter (isClosed_imp (S := {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}) ?_) (isClosed_imp (S := {z : ℂ | ‖z‖ ≤ 1}) ?_))
      · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
      · exact isClosed_le continuous_norm continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
      rintro z ⟨h1, h2, h3⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rcases lt_trichotomy a b with h | h | h
      · linarith [h3 h]
      · exact (h2 h).2
      · rw [h1 h, norm_zero]
        norm_num
  have e : CmatSet X = Set.pi Set.univ fun τ => Set.pi Set.univ fun a => Set.pi Set.univ fun b =>
      {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    ext β
    simp [CmatSet, Set.mem_pi]
  rw [e]
  exact isCompact_univ_pi fun τ => isCompact_univ_pi fun a => isCompact_univ_pi fun b => hS a b

lemma continuous_entry {α : Type*} [TopologicalSpace α] {f : α → Frame X.Ψ r}
    (hf : ∀ τ a b, Continuous fun y => f y τ a b) :
    Continuous f := continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => hf τ a b

def gramF (y : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gram τ.1 X.Gm (mat y τ)

def gramTF (β : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gramT X (mat β τ)

lemma continuous_gramF : Continuous (gramF X) := by
  apply continuous_entry
  intro τ a b
  simp only [gramF, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mat]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_coord X τ i a).mul continuous_const).mul (Complex.continuous_conj.comp (continuous_coord X τ j b))

lemma continuous_gramTF : Continuous (gramTF X) := by
  apply continuous_entry
  intro τ a b
  simp only [gramTF, gramT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mat, Matrix.of_apply]
  exact continuous_finset_sum _ fun l _ =>
    (continuous_finset_sum _ fun k _ => (continuous_coord X τ k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_coord X τ l b))

private lemma isOpen_X_dom : IsOpen X.dom := by
  have e : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [e]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact isOpen_ne_fun hm.matrix_det continuous_const
  · have hg : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) :=
      (continuous_apply τ).comp (continuous_gramF X)
    have hc : Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      unfold dmin lminor
      exact Complex.continuous_re.comp (hg.matrix_submatrix _ _).matrix_det
    exact isOpen_lt continuous_const (continuous_const.mul hc)

lemma measurableSet_SW : MeasurableSet (SW X) := by
  have e : SW X = X.dom ∩ gramF X ⁻¹' (gramTF X '' CmatSet X) := by
    ext y
    simp only [SW, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, funext fun τ => (hg τ).symm⟩
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, fun τ => (congrFun hg τ).symm⟩
  rw [e]
  have h1 : MeasurableSet X.dom := (isOpen_X_dom X).measurableSet
  have h2 : IsClosed (gramF X ⁻¹' (gramTF X '' CmatSet X)) :=
    ((isCompact_CmatSet X).image (continuous_gramTF X)).isClosed.preimage (continuous_gramF X)
  exact h1.inter h2.measurableSet

lemma measurable_Wf : Measurable (Wf X) := measurable_one.indicator (measurableSet_SW X)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset

noncomputable section

attribute [local instance] Classical.propDecidable

lemma prod_min_range (f : ℕ → ℝ) (n : ℕ) :
    ∏ a ∈ range n, ∏ b ∈ range n, f (min a b) = (∏ i ∈ range n, (∏ k ∈ range i, f k) ^ 2) * ∏ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ a ∈ range n, ∏ b ∈ range (n + 1), f (min a b) = (∏ b ∈ range n, f (min a b)) * f a := by
      intro a ha
      rw [prod_range_succ, min_eq_left (le_of_lt (mem_range.mp ha))]
    have h2 : ∏ b ∈ range (n + 1), f (min n b) = (∏ b ∈ range n, f b) * f n := by
      rw [prod_range_succ, min_self]
      congr 1
      exact prod_congr rfl fun b hb => by rw [min_eq_right (le_of_lt (mem_range.mp hb))]
    rw [prod_range_succ (fun a => ∏ b ∈ range (n + 1), f (min a b)) n, prod_congr rfl h1, prod_mul_distrib, ih, h2,
      prod_range_succ (fun i => (∏ k ∈ range i, f k) ^ 2) n, prod_range_succ f n]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma upper_mul_diag {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (k : Fin r) : (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma bOf_diag (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : mat (bOf X y) τ k k = sOf X y τ k := by
  have h1 : mat (bOf X y) τ k k = uOf X y τ k k * sOf X y τ k := by
    show (uOf X y τ * Matrix.diagonal (sOf X y τ)) k k = _
    rw [Matrix.mul_diagonal]
  rw [h1]
  have h2 : uOf X y τ k k = 1 := by
    show uMat _ k k = 1
    unfold uMat
    simp
  rw [h2, one_mul]

lemma normSq_β0_diag {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by
  have hinv : β0 X y τ * mat (bOf X y) τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  have h1 := congrFun (congrFun hinv k) k
  rw [upper_mul_diag (β0_upper X hy τ) (upper_of_bor X (bOf_mem X hy) τ), bOf_diag, Matrix.one_apply_eq] at h1
  have hpos := abs_re_pos X hy τ k
  have hs : Complex.normSq (sOf X y τ k) = |(dOf X y τ k).re|⁻¹ := by
    rw [sOf, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_mul, hs, map_one] at h2
  field_simp at h2
  linarith

def δ (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℝ := |(dOf X y τ k).re|

def fδ (y : Frame X.Ψ r) (τ : X.Ψ) (k : ℕ) : ℝ := if h : k < r then δ X y τ ⟨k, h⟩ else 1

lemma normSq_det_jac {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ i : Ix X.Ψ r, δ X y i.1 (min i.2.1 i.2.2) := by
  rw [det_Lβ _ (β0_upper X hy), jacβ, map_prod, map_prod]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => δ X y i.1 (min i.2.1 i.2.2))]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => Complex.normSq (if i.2.2 < i.2.1 then β0 X y i.1 i.2.2 i.2.2 else 1))]
  have e1 : ∏ i : UpI X.Ψ r, Complex.normSq (β0 X y i.1.1 i.1.2.1 i.1.2.1) =
      ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [normSq_β0_diag X hy, min_eq_left (not_lt.1 i.2)]; rfl
  have e2 : ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [if_neg i.2, map_one]
  have e3 : ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) =
      ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [if_pos i.2, normSq_β0_diag X hy, min_eq_right i.2.le]; rfl
  rw [e1, e2, e3, mul_one, mul_comm]

lemma norm_dmin {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = ∏ k ∈ range i, fδ X y τ k := by
  rw [dmin_prod X hy τ i, norm_prod, ← Fin.prod_univ_eq_prod_range (fδ X y τ)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)
  rw [fδ, dif_pos hj, δ]
  have hre := dOf_real X hy τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  have hc : Fin.castLE (Nat.le_of_lt_succ i.isLt) j = (⟨j, hj⟩ : Fin r) := Fin.ext rfl
  rw [hc] at hre ⊢
  exact (Complex.abs_re_eq_norm.2 hre).symm

theorem exponent_identity {y : Frame X.Ψ r} (hy : y ∈ X.dom) (hlast : ∀ τ, ‖dmin X.Gm y τ (Fin.last r)‖ = 1) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
  have hτ : ∀ τ : X.Ψ, ∏ a : Fin r, ∏ b : Fin r, δ X y τ (min a b) =
      ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
    intro τ
    have hp := prod_min_range (fδ X y τ) r
    have hl : ∏ k ∈ range r, fδ X y τ k = 1 := by
      have h1 := norm_dmin X hy τ (Fin.last r)
      rw [hlast τ, Fin.val_last] at h1
      exact h1.symm
    rw [hl, mul_one] at hp
    have hd : ∀ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ = ∏ k ∈ range (i : ℕ), fδ X y τ k := by
      intro i
      rw [norm_dmin X hy τ i.castSucc, Fin.coe_castSucc]
    have e1 : ∀ a b : Fin r, δ X y τ (min a b) = fδ X y τ (min (a : ℕ) (b : ℕ)) := by
      intro a b
      unfold fδ
      rw [dif_pos (min_lt_of_left_lt a.isLt)]
      congr 1
    simp only [hd, e1]
    simp only [Finset.prod_range] at hp ⊢
    exact hp
  rw [normSq_det_jac X hy]
  unfold Ix
  simp only [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun τ _ => hτ τ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end
