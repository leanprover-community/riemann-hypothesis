module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardValLt

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.CartanDom

theorem det_mul_eq_sum_fun {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

theorem prod_zpow_eq {G : Type*} [CommGroupWithZero G] {ι : Type*} (s : Finset ι) {x : G} (hx : x ≠ 0)
    (e : ι → ℤ) : ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hx, ih]

theorem sum_le_sum_of_threshold {α : Type*} [DecidableEq α] (e : α → ℤ) (U T : Finset α) (hc : T.card = U.card)
    (c : ℤ) (hU : ∀ i ∈ U, e i ≤ c) (hU' : ∀ i ∈ T, i ∉ U → c ≤ e i) : ∑ i ∈ U, e i ≤ ∑ i ∈ T, e i := by
  have h1 : ∑ i ∈ U ∩ T, (c - e i) ≤ ∑ i ∈ U, (c - e i) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun i hi _ => by linarith [hU i hi])
  have h2 : ∑ i ∈ U ∩ T, (e i - c) ≤ ∑ i ∈ T, (e i - c) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i hi hni => by
      have : i ∉ U := fun h => hni (Finset.mem_inter.2 ⟨h, hi⟩)
      linarith [hU' i hi this])
  simp only [Finset.sum_sub_distrib, Finset.sum_const, smul_eq_mul] at h1 h2
  rw [hc] at h2
  linarith

theorem sum_tail_le {N : ℕ} (e : Fin N → ℤ) (he : Antitone e) (j : ℕ) (hj : j < N)
    (f : {i : Fin N // ¬ (i : ℕ) < j} → Fin N) (hf : Function.Injective f) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), e i ≤ ∑ x, e (f x) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (fun a _ b _ h => hf h)]
  refine sum_le_sum_of_threshold e _ _ ?_ (e ⟨j, hj⟩) ?_ ?_
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_subtype]
  · intro i hi
    exact he (Fin.le_iff_val_le_val.2 (by simp at hi; simpa using hi))
  · intro i _ hi
    exact he (Fin.le_iff_val_le_val.2 (by simp at hi; simp; omega))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (hM : ∀ i j, valuation k (M i j) ≤ 1) : valuation k M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul, map_prod]; exact Finset.prod_le_one' fun i _ => hM _ _
  · rw [Units.neg_smul, one_smul, Valuation.map_neg, map_prod]; exact Finset.prod_le_one' fun i _ => hM _ _

theorem minor_mul_int {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (X A : Matrix m m k)
    (γ : ValueGroupWithZero k) (hA : ∀ i j, valuation k (A i j) ≤ 1)
    (hX : ∀ f h : ι → m, valuation k (X.submatrix f h).det ≤ γ) (f h : ι → m) :
    valuation k ((X * A).submatrix f h).det ≤ γ := by
  have e : (X * A).submatrix f h = X.submatrix f id * A.submatrix id h := by
    ext a b; simp [Matrix.mul_apply]
  rw [e, det_mul_eq_sum_fun]
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  calc _ ≤ 1 * γ := mul_le_mul' (Finset.prod_le_one' fun i _ => hA _ _)
          (by simpa [Matrix.submatrix_submatrix] using hX f σ)
    _ = γ := one_mul γ

theorem minor_int_mul {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (A X : Matrix m m k)
    (γ : ValueGroupWithZero k) (hA : ∀ i j, valuation k (A i j) ≤ 1)
    (hX : ∀ f h : ι → m, valuation k (X.submatrix f h).det ≤ γ) (f h : ι → m) :
    valuation k ((A * X).submatrix f h).det ≤ γ := by
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_mul]
  exact minor_mul_int Xᵀ Aᵀ γ (fun i j => hA j i)
    (fun f h => by rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact hX h f) h f

theorem det_diag_mul_submatrix {m ι : Type*} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]
    (d : m → k) (M : Matrix m m k) (f h : ι → m) :
    ((diagonal d * M).submatrix f h).det = (∏ x, d (f x)) * (M.submatrix f h).det := by
  have e : (diagonal d * M).submatrix f h = diagonal (fun x => d (f x)) * M.submatrix f h := by
    ext a b; simp [diagonal_mul]
  rw [e, det_mul, det_diagonal]

theorem det_submatrix_eq_zero {m ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix m m k) (f h : ι → m)
    (hf : ¬ Function.Injective f) : (M.submatrix f h).det = 0 := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, h1, h2⟩ := hf
    exact ⟨a, b, h1, h2⟩
  exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hab])

theorem KO_int {m : Type} [Fintype m] [DecidableEq m] {κ : GL m k} (hκ : κ ∈ KO k m) (i j : m) :
    valuation k (κ.1 i j) ≤ 1 := by
  obtain ⟨κ₀, rfl⟩ := hκ
  exact (κ₀.1 i j).2

theorem KO_det {m : Type} [Fintype m] [DecidableEq m] {κ : GL m k} (hκ : κ ∈ KO k m) :
    valuation k κ.1.det = 1 := by
  have h1 := val_det_le_one _ (KO_int hκ)
  have h2 := val_det_le_one _ (KO_int (inv_mem hκ))
  have h3 : valuation k κ.1.det * valuation k (κ⁻¹).1.det = 1 := by
    rw [← map_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, map_one]
  by_contra hne
  have hlt : valuation k κ.1.det < 1 := lt_of_le_of_ne h1 hne
  have : valuation k κ.1.det * valuation k (κ⁻¹).1.det < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  rw [h3] at this
  exact lt_irrefl _ this

theorem card_filter_lt (N n : ℕ) (hn : n ≤ N) : (Finset.univ.filter fun i : Fin N => (i : ℕ) < n).card = n := by
  first
  | exact @_root_.GlobalTheory.CardValuationLt.card_val_lt
  | exact _root_.GlobalTheory.CardValuationLt.card_val_lt
  | (apply _root_.GlobalTheory.CardValuationLt.card_val_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.CardValuationLt.card_val_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CardValuationLt.card_val_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CardValuationLt.card_val_lt ..)

theorem indic_antitone (N n : ℕ) : Antitone (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) := by
  intro a b hab
  simp only [indic, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (a : ℕ) ≤ b := hab
  split_ifs <;> omega

theorem sum_indic (N n : ℕ) (hn : n ≤ N) :
    ∑ i : Fin N, indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i = n := by
  simp only [indic, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast card_filter_lt N n hn

theorem val_torus_prod (ϖ : kˣ) {ι : Type*} [Fintype ι] (e : ι → ℤ) :
    valuation k (∏ x, (ϖ : k) ^ e x) = valuation k (ϖ : k) ^ ∑ x, e x := by
  rw [map_prod]
  simp_rw [map_zpow₀]
  exact prod_zpow_eq _ ((Valuation.ne_zero_iff _).2 ϖ.ne_zero) e

theorem tail_diag {N : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (j : ℕ) (hj : j < N) (M : Matrix (Fin N) (Fin N) k) (γ : ValueGroupWithZero k)
    (hM : ∀ f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N, valuation k (M.submatrix f h).det ≤ γ)
    (f h : {i : Fin N // ¬ (i : ℕ) < j} → Fin N) :
    valuation k (((diagonal fun i => (ϖ : k) ^ e i) * M).submatrix f h).det ≤
      valuation k (ϖ : k) ^ (∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), e i) * γ := by
  rw [det_diag_mul_submatrix]
  by_cases hf : Function.Injective f
  · rw [map_mul, val_torus_prod]
    have hw1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
    have hw0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
    exact mul_le_mul' ((zpow_le_zpow_iff_right_of_lt_one₀ hw0 hw1).2 (sum_tail_le e he j hj f hf)) (hM f h)
  · rw [det_submatrix_eq_zero _ _ _ hf, mul_zero, map_zero]
    exact zero_le'

end GlobalTheory.CartanDom

end
