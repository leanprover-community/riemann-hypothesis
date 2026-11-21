import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrix

section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  intro Y hY
  rw [eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)]
  exact hU

theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
end
end

section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_box_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k), Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧ ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  first | exact @GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | exact GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn | (intros; apply GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn <;> assumption)
end

section
open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := GlobalTheory.T.matrix_rank_normal_form k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end

section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_rank_ge : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  first | exact @GlobalTheory.isOpen_setOf_le_rank_localField | exact GlobalTheory.isOpen_setOf_le_rank_localField | (intros; apply GlobalTheory.isOpen_setOf_le_rank_localField <;> assumption)
end

section
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem exists_KO_row_zero_of_rank_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (X : Matrix A D k) (hX : X.rank < Fintype.card A) :
    ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by

  have hdep : ¬ LinearIndependent k X.row := by
    intro h
    rw [linearIndependent_iff_card_eq_finrank_span] at h
    rw [rank_eq_finrank_span_row] at hX
    exact (lt_irrefl _) (h ▸ hX)
  obtain ⟨c, hc, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hcj : ∀ j, ∑ i, c i * X i j = 0 := by
    intro j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.row] using this

  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (c i))
    ⟨i₁, Finset.mem_univ _⟩
  have hc0 : c i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set c' : A → k := fun i => c i / c i₀ with hc'
  have hc'int : ∀ i, c' i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff, hc', map_div₀]
    have hpos : 0 < valuation k (c i₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hc0
    exact (div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))
  have hc'0 : c' i₀ = 1 := div_self hc0

  let E : Matrix A A k := Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0
  have hEE : E * E = 0 := by
    ext i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i₀
    · simp [hl]
    · simp [hl]
  have hEint : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [E, Matrix.of_apply]
    split_ifs
    · exact hc'int j
    · exact zero_mem _
  have h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let g : GL A k := ⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩
  refine ⟨g, ?_, i₀, fun j => ?_⟩
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      exact add_mem (h1int i j) (hEint i j)
    · show (1 - E) i j ∈ 𝒪[k]
      exact sub_mem (h1int i j) (hEint i j)
  · show (((1 : Matrix A A k) + E) * X) i₀ j = 0
    have hrow : ∀ l, (1 + E) i₀ l = c' l := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simp [E, hc'0]
      · simp [E, hl, Matrix.one_apply, Ne.symm hl]
    rw [Matrix.mul_apply]
    simp_rw [hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]

end GlobalTheory.RankCoinv
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_integral_row_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D k), X.rank < Fintype.card A → ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by
  atlas_forward_decl GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt
end

section
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem frame_normalise_integral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ)
    (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k) (hYQ : Y * Q' = 1) :
    ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k),
      (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  classical

  have key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det := by
    simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [hYQ, det_one] at key
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)
  haveI : Nonempty (Fin s → D) := ⟨p₀⟩
  obtain ⟨κ, hκ⟩ := Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)
  have hne : (Y.submatrix id κ).det ≠ 0 := by
    intro h0
    have := hκ p₀
    rw [h0, map_zero] at this
    exact right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))
  set h := (Y.submatrix id κ)⁻¹ with hh
  have hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p := by
    intro p; ext r c; simp [mul_apply]
  have hone : (h * Y).submatrix id κ = 1 := by
    rw [hsub, hh]
    exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
  refine ⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩
  · intro i j
    have e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det := by
      have : (h * Y).submatrix id (Function.update κ i j) =
          (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j) := by
        ext r c
        by_cases hc : c = i
        · subst hc; simp
        · rw [updateCol_ne hc, ← hone]
          simp [Function.update_of_ne hc]
      rw [this, ← cramer_apply, cramer_one]; rfl
    rw [Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀]
    have hpos : 0 < valuation k (Y.submatrix id κ).det :=
      lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))
    rw [mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hκ _
  · intro i j
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · have : h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) =
        (h * Y).submatrix id κ := by
      ext r l; simp [mul_apply]
    rw [this, hone]

end GlobalTheory
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_inverse_normalization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ) (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k), Y * Q' = 1 → ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k), (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  atlas_forward_decl GlobalTheory.frame_normalise_integral
end

section
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem omA_diag_boxFn_succ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ C hC m n
  have hdet : GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ)) = ϖ := by
    rw [GlobalTheory.SplitFlip.gdet, GlobalTheory.SplitFlip.det_diagGL, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hinv : ((GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ))⁻¹).val =
      diagonal fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k) := rfl
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have key : ∀ X : Matrix A D k,
      (diagonal (fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k)) * X) ∈
        box ϖ C (Function.update (fun _ => m) i₀ n) ↔ X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
    intro X
    simp only [box, Set.mem_setOf_eq, diagonal_mul]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, hC, sub_zero, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        pow_succ, Units.val_mul, map_mul, map_inv₀, map_pow]
      rw [inv_mul_le_iff₀ h0, mul_comm (valuation k (ϖ : k))]
    · simp [Function.update_of_ne hi]
  funext X
  rw [GlobalTheory.RankCoinv.omA_one_apply, hdet, Pi.smul_apply, smul_eq_mul, hinv]
  congr 1
  unfold boxFn
  by_cases hX : X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1))
  · rw [Set.indicator_of_mem ((key X).2 hX), Set.indicator_of_mem hX]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hX ((key X).1 h)), Set.indicator_of_notMem hX]

end GlobalTheory.RankCoinv
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_diagonal_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  atlas_forward_decl GlobalTheory.RankCoinv.omA_diag_boxFn_succ
end

section
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_of_add_vecMul {r : ℕ} {u t : ValueGroupWithZero k} (hu : u < 1) (s : Fin r → k)
    (E : Matrix (Fin r) (Fin r) k) (hE : ∀ l j, valuation k (E l j) ≤ u)
    (hw : ∀ l, valuation k ((s + s ᵥ* E) l) ≤ t) (l : Fin r) : valuation k (s l) ≤ t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨l₁, -, hl₁⟩ := Finset.exists_max_image Finset.univ (fun j => valuation k (s j)) ⟨l, Finset.mem_univ _⟩
  have hM : t < valuation k (s l₁) := hlt.trans_le (hl₁ l (Finset.mem_univ _))
  have hM0 : 0 < valuation k (s l₁) := lt_of_le_of_lt zero_le' hM
  have h1 : valuation k ((s ᵥ* E) l₁) ≤ valuation k (s l₁) * u := by
    simp only [Matrix.vecMul, dotProduct]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hl₁ j (Finset.mem_univ _)) (hE j l₁)
  have h3 := Valuation.map_sub_le (valuation k) ((hw l₁).trans (le_max_left t (valuation k (s l₁) * u)))
    (h1.trans (le_max_right _ _))
  rw [Pi.add_apply, add_sub_cancel_right] at h3
  have h4 : valuation k (s l₁) * u < valuation k (s l₁) := mul_lt_of_lt_one_right hM0 hu
  rcases le_max_iff.1 h3 with h | h
  · exact absurd h (not_le.2 hM)
  · exact absurd h (not_le.2 h4)

theorem val_pow (ϖ : kˣ) (n : ℕ) : valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

theorem mem_max_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 ↔ valuation k (x : k) ≤ valuation k (ϖ : k) := by
  rw [pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  exact Iff.rfl

variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

omit [Fintype A] [Fintype D] [DecidableEq D] in

theorem mem_box_update {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (hC : ∀ j, C i₀ j = 0) :
    X ∈ box ϖ C (Function.update (fun _ => m) i₀ (m - 1)) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [Function.update_of_ne hi] using h i j, fun j => by simpa [hC] using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa [hC] using h2 j
    · simpa [Function.update_of_ne hi] using h1 i hi j

omit [Fintype A] [Fintype D] [DecidableEq D] in

theorem mem_box_updateRow {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (R : D → k) :
    X ∈ box ϖ (C.updateRow i₀ R) (fun _ => m) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j - R j) ≤ valuation k (ϖ : k) ^ m := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [updateRow_ne hi] using h i j, fun j => by simpa using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa using h2 j
    · simpa [updateRow_ne hi] using h1 i hi j

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type} [Fintype D] [DecidableEq D]

def shiftRow (ϖ : kˣ) (m : ℕ) {r : ℕ} (b : Fin r → Res k 1) : Fin r → k :=
  fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)

theorem inv_pow_mul_pow_le {u : ValueGroupWithZero k} (hu : u < 1) (hu0 : u ≠ 0) {c m : ℕ} (hcm : c + 1 ≤ m) :
    (u ^ c)⁻¹ * u ^ m ≤ u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = c + 1 + n := ⟨m - (c + 1), by omega⟩
  rw [pow_add, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]
  exact mul_le_of_le_one_right' (pow_le_one' hu.le n)

omit [DecidableEq D] in

theorem val_shiftRow_le (ϖ : kˣ) {r m : ℕ} (Y : Matrix (Fin r) D k) (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (b : Fin r → Res k 1) (j : D) :
    valuation k ((shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [Matrix.vecMul, dotProduct, shiftRow]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul, map_pow]
  calc _ ≤ valuation k (ϖ : k) ^ (m - 1) * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 (Quotient.out (b l)).2))
          ((Valuation.mem_integer_iff _ _).1 (hY l j))
    _ = _ := by rw [mul_one, mul_one]

omit [DecidableEq D] in

theorem shiftRow_unique {ϖ : kˣ} (hϖ : IsUnif ϖ) {r m : ℕ} (hm : 1 ≤ m) (Y : Matrix (Fin r) D k)
    (Q : Matrix D (Fin r) k) (hQ : ∀ j l, Q j l ∈ 𝒪[k]) (hYQ : Y * Q = 1) (x : D → k)
    (b b' : Fin r → Res k 1)
    (hb : ∀ j, valuation k (x j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m)
    (hb' : ∀ j, valuation k (x j - (shiftRow ϖ m b' ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m) :
    b = b' := by
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  let δ : Fin r → k := fun l =>
    (ϖ : k) ^ (m - 1) * (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k))
  have hδ : δ ᵥ* Y = shiftRow ϖ m b ᵥ* Y - shiftRow ϖ m b' ᵥ* Y := by
    rw [← Matrix.sub_vecMul]; congr 1; funext l; simp [δ, shiftRow, mul_sub]
  have h1 : ∀ j, valuation k ((δ ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := fun j => by
    have := Valuation.map_sub_le (valuation k) (hb' j) (hb j)
    rwa [sub_sub_sub_cancel_left, ← Pi.sub_apply, ← hδ] at this
  have h2 : δ = (δ ᵥ* Y) ᵥ* Q := by rw [Matrix.vecMul_vecMul, hYQ, Matrix.vecMul_one]
  have h3 : ∀ l, valuation k (δ l) ≤ valuation k (ϖ : k) ^ m := fun l => by
    rw [h2]
    show valuation k (∑ j, (δ ᵥ* Y) j * Q j l) ≤ _
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_mul' (h1 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
  funext l
  have h4 : valuation k (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k)) ≤
      valuation k (ϖ : k) := by
    have h5 := h3 l
    have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
      rw [← pow_succ]; congr 1; omega
    simp only [δ, map_mul, map_pow] at h5
    rw [hm'] at h5
    exact (mul_le_mul_iff_right₀ (zero_lt_iff.2 (pow_ne_zero _ hu0))).1 h5
  rw [← Ideal.Quotient.mk_out (b l), ← Ideal.Quotient.mk_out (b' l)]
  exact Ideal.Quotient.eq.2 ((mem_max_iff hϖ _).2 h4)

omit [DecidableEq D] in

theorem shiftRow_exists {ϖ : kˣ} (hϖ : IsUnif ϖ) {r c m : ℕ} (hcm : c + 1 ≤ m) (Y Z : Matrix (Fin r) D k)
    (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (hZ : ∀ l j, valuation k (Z l j) ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m)
    (s : Fin r → k) (hs : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1)) :
    ∃ b : Fin r → Res k 1, ∀ j,
      valuation k ((s ᵥ* (Y + Z)) j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := by
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hp0 : (ϖ : k) ^ (m - 1) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hvp : 0 < valuation k (ϖ : k) ^ (m - 1) := zero_lt_iff.2 (pow_ne_zero _ hu0)
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have htt : ∀ l, ((ϖ : k) ^ (m - 1))⁻¹ * s l ∈ 𝒪[k] := fun l => by
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀, map_pow, inv_mul_le_iff₀ hvp, mul_one]; exact hs l
  let b₀ : Fin r → Res k 1 := fun l => Ideal.Quotient.mk _ ⟨_, htt l⟩
  have hb : ∀ l, valuation k (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l) ≤
      valuation k (ϖ : k) :=
    fun l => (mem_max_iff hϖ _).1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (b₀ l)))
  refine ⟨b₀, fun j => ?_⟩
  have e : (s ᵥ* (Y + Z)) j - (shiftRow ϖ m b₀ ᵥ* Y) j = ((s - shiftRow ϖ m b₀) ᵥ* Y) j + (s ᵥ* Z) j := by
    rw [Matrix.vecMul_add, Matrix.sub_vecMul]; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · show valuation k (∑ l, (s - shiftRow ϖ m b₀) l * Y l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    have e2 : (s - shiftRow ϖ m b₀) l = -((ϖ : k) ^ (m - 1) *
        (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l)) := by
      simp only [Pi.sub_apply, shiftRow]; rw [mul_sub, mul_inv_cancel_left₀ hp0]; ring
    rw [e2, map_mul, Valuation.map_neg, map_mul, map_pow, hm']
    exact (mul_le_mul' (mul_le_mul' le_rfl (hb l)) ((Valuation.mem_integer_iff _ _).1 (hY l j))).trans
      (by rw [mul_one])
  · show valuation k (∑ l, s l * Z l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, hm']
    exact mul_le_mul' (hs l) ((hZ l j).trans (inv_pow_mul_pow_le hu hu0 hcm))

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

theorem boxFn_sub_sum_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hY hQ hYQ hC0
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have hmm : valuation k (ϖ : k) ^ m ≤ valuation k (ϖ : k) ^ (m - 1) := by
    rw [hm']; exact mul_le_of_le_one_right' hu.le
  have hHv' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k) ^ c)⁻¹ := fun l i => by
    have := hHv l i
    rwa [Units.val_inv_eq_inv_val, map_inv₀, val_pow] at this
  rw [mem_lowRank]
  refine ⟨sub_mem (boxFn_mem_SB _ _ _) (Submodule.sum_mem _ fun b _ => boxFn_mem_SB _ _ _), fun X hX => ?_⟩
  have hXr : X.rank ≤ r := Nat.lt_succ_iff.1 hX
  simp only [Pi.sub_apply, Finset.sum_apply, boxFn]
  rw [sub_eq_zero]
  change _ = ∑ b : Fin r → Res k 1, (box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) fun _ => m).indicator 1 X
  by_cases hrows : ∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m
  · by_cases hi0 : ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1)
    · let E : Matrix (Fin r) (Fin r) k := H * (X - C) * Q
      have hHXC : ∀ l j, valuation k ((H * (X - C)) l j) ≤
          (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m := by
        intro l j
        rw [Matrix.mul_apply]
        refine Valuation.map_sum_le _ fun i _ => ?_
        by_cases hi : i = i₀
        · subst hi; simp [hH0]
        · rw [map_mul]; exact mul_le_mul' (hHv' l i) (by simpa [Matrix.sub_apply] using hrows i hi j)
      have hE : ∀ l j, valuation k (E l j) ≤ valuation k (ϖ : k) := by
        intro l j
        refine (?_ : _ ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m).trans
          (inv_pow_mul_pow_le hu hu0 hcm)
        show valuation k (∑ a, (H * (X - C)) l a * Q a j) ≤ _
        refine Valuation.map_sum_le _ fun a _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hHXC l a) ((Valuation.mem_integer_iff _ _).1 (hQ a j))).trans (by rw [mul_one])
      have hHXQ : H * X * Q = 1 + E := by
        simp only [E, Matrix.mul_sub, Matrix.sub_mul, hYQ]; abel
      have hunit : IsUnit (H * X * Q) := by
        rw [← vecMul_injective_iff_isUnit]
        intro s s' hss
        have h0 : (s - s') + (s - s') ᵥ* E = 0 := by
          have : (s - s') ᵥ* (H * X * Q) = 0 := by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hss
          rwa [hHXQ, Matrix.vecMul_add, Matrix.vecMul_one] at this
        funext l
        have := val_le_of_add_vecMul hu (s - s') E hE (t := 0) (fun l => by rw [h0]; simp) l
        exact sub_eq_zero.1 ((Valuation.zero_iff _).1 (le_zero_iff.1 this))
      obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X H Q hXr hunit i₀
      have hsv : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1) := by
        refine val_le_of_add_vecMul hu s E hE fun l => ?_
        have e : s + s ᵥ* E = X i₀ ᵥ* Q := by
          rw [hs, Matrix.vecMul_vecMul, hHXQ, Matrix.vecMul_add, Matrix.vecMul_one]
        rw [e]
        show valuation k (∑ j, X i₀ j * Q j l) ≤ _
        refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hi0 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
      have hXs : X i₀ = s ᵥ* (H * C + H * (X - C)) := by
        rw [hs]; congr 1; rw [Matrix.mul_sub]; abel
      obtain ⟨b₀, hb₀⟩ := shiftRow_exists hϖ hcm (H * C) (H * (X - C)) hY hHXC s hsv
      rw [← hXs] at hb₀
      have hmem : ∀ b, X ∈ box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) (fun _ => m) ↔ b = b₀ := fun b =>
        ⟨fun h => shiftRow_unique hϖ (by omega) (H * C) Q hQ hYQ (X i₀) b b₀ ((mem_box_updateRow _).1 h).2 hb₀,
          fun h => h ▸ (mem_box_updateRow _).2 ⟨hrows, hb₀⟩⟩
      rw [Set.indicator_of_mem ((mem_box_update hC0).2 ⟨hrows, hi0⟩), Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun h => hb ((hmem b).1 h)) _) (by simp),
        Set.indicator_of_mem ((hmem b₀).2 rfl)]
    · rw [Set.indicator_of_notMem (fun h => hi0 ((mem_box_update hC0).1 h).2)]
      refine (Finset.sum_eq_zero fun b _ => Set.indicator_of_notMem (fun h => hi0 fun j => ?_) _).symm
      have h2 := ((mem_box_updateRow _).1 h).2 j
      rw [← sub_add_cancel (X i₀ j) ((shiftRow ϖ m b ᵥ* (H * C)) j)]
      exact Valuation.map_add_le _ (h2.trans hmm) (val_shiftRow_le ϖ (H * C) hY b j)
  · rw [Set.indicator_of_notMem (fun h => hrows ((mem_box_update hC0).1 h).1)]
    exact (Finset.sum_eq_zero fun b _ =>
      Set.indicator_of_notMem (fun h => hrows ((mem_box_updateRow _).1 h).1) _).symm

end GlobalTheory.CountTranslates
end
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_box_bounded_valuation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  atlas_forward_decl GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank
end

section
section
open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → Res k 1) with hN
  let F : (Fin r → Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := GlobalTheory.T.box_function_diagonal_action k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    GlobalTheory.T.integral_box_bounded_valuation k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  atlas_forward_decl GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row
end

section
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant_rank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  atlas_forward_decl GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row
end

section
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Nbhd

section
variable {k : Type} [Field k] {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (v : Valuation k Γ)
variable {X Y W : Type} [Fintype Y]

theorem val_mul_le {P : Matrix X Y k} {Z : Matrix Y W k} {s t : Γ} (hP : ∀ i a, v (P i a) ≤ s)
    (hZ : ∀ a j, v (Z a j) ≤ t) (i : X) (j : W) : v ((P * Z) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun a _ => ?_
  rw [map_mul]; exact mul_le_mul' (hP i a) (hZ a j)
end

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_inv_pow (ϖ : kˣ) (c : ℕ) :
    valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) = (valuation k (ϖ : k))⁻¹ ^ c := by
  simp [Units.val_inv_eq_inv_val, map_inv₀, map_pow, inv_pow]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (x : k) :
    ∃ c : ℕ, valuation k x ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  by_cases h : valuation k x ≤ 1
  · exact ⟨0, by simpa using h⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have h0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
    have hy : valuation k x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      calc (valuation k x)⁻¹ = (valuation k x)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (valuation k x)⁻¹ * valuation k x := mul_le_mul' le_rfl (le_of_not_ge h)
        _ = 1 := inv_mul_cancel₀ h0.ne'
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := 𝒪[k])
      (x := ⟨x⁻¹, hy⟩) (fun h' => hx (inv_eq_zero.1 (congrArg Subtype.val h'))) hϖ.irreducible
    refine ⟨n, ?_⟩
    have h1 : valuation k (algebraMap 𝒪[k] k u) = 1 :=
      (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have h2 : valuation k x⁻¹ = valuation k (ϖ : k) ^ n := by
      have := congrArg (fun y : 𝒪[k] => valuation k (y : k)) hu
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
      rw [this]
      have h1' : valuation k ((u : 𝒪[k]) : k) = 1 := h1
      rw [h1', one_mul]
    rw [valuation_inv_pow, inv_pow, ← h2, map_inv₀, inv_inv]

theorem exists_bound {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {R S : Type} [Fintype R] [Fintype S]
    (H : Matrix R S k) : ∃ c : ℕ, ∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  choose f hf using fun p : R × S => exists_le_inv_pow hϖ (H p.1 p.2)
  refine ⟨Finset.univ.sup f, fun l i => (hf (l, i)).trans ?_⟩
  rw [valuation_inv_pow, valuation_inv_pow]
  have hle : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : 1 ≤ (valuation k (ϖ : k))⁻¹ :=
    calc (1 : _) = valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ 1 * (valuation k (ϖ : k))⁻¹ := mul_le_mul' hle le_rfl
      _ = _ := one_mul _
  exact pow_le_pow_right₀ h1 (Finset.le_sup (f := f) (Finset.mem_univ (l, i)))

theorem exists_int_inv_one_add {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) = (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

end GlobalTheory.RankCoinv.Nbhd

namespace GlobalTheory.RankCoinv.Nbhd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem inv_mul_mem_box_iff {g : GL A k} (hg : g ∈ KO k A) (ϖ : kˣ) (C X : Matrix A D k) (m : ℕ) :
    (g⁻¹).val * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ (g.val * C) (fun _ => m) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  have h1' : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h1 i a)
  have h2' : ∀ i a, valuation k ((g⁻¹).val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h2 i a)
  simp only [box, Set.mem_setOf_eq]
  constructor
  · intro hZ i j
    have e : X i j - (g.val * C) i j = (g.val * ((g⁻¹).val * X - C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h1' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)
  · intro hZ i j
    have e : ((g⁻¹).val * X) i j - C i j = ((g⁻¹).val * (X - g.val * C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h2' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)

theorem omA_boxFn {g : GL A k} (hg : g ∈ KO k A) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (C : Matrix A D k) (m : ℕ) :
    ∃ s : ℂ, omA ν β g 1 (boxFn ϖ C (fun _ => m)) = s • boxFn ϖ (g.val * C) (fun _ => m) := by
  refine ⟨(((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2), funext fun X => ?_⟩
  rw [omA_one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases h : X ∈ box ϖ (g.val * C) (fun _ => m)
  · simp only [boxFn]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ((inv_mul_mem_box_iff hg ϖ C X m).2 h)]
    rfl
  · simp only [boxFn]
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((inv_mul_mem_box_iff hg ϖ C X m).1 h'))]

end GlobalTheory.RankCoinv.Nbhd

open GlobalTheory.RankCoinv.Nbhd GlobalTheory.SplitFlip GlobalTheory.SplitWeil in

theorem GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r X₀ hrank hr
  obtain ⟨g, hg, i₀, hi₀⟩ := GlobalTheory.T.rank_deficient_integral_row_reduction k A D X₀ (hrank ▸ hr)
  have hgint := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hg1 : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (hgint.1 i a)
  have hYr : (g.val * X₀).rank = r := by
    rw [← hrank]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨H₁, Q₁, hHQ⟩ : ∃ (H₁ : Matrix (Fin r) A k) (Q₁ : Matrix D (Fin r) k), H₁ * (g.val * X₀) * Q₁ = 1 := by
    rw [← hYr]; exact GlobalTheory.T.matrix_rank_normal_form k A D _
  let H₂ : Matrix (Fin r) A k := Matrix.of fun l i => if i = i₀ then 0 else H₁ l i
  have hH₂Y : H₂ * (g.val * X₀) = H₁ * (g.val * X₀) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H₂, Matrix.of_apply]
    split_ifs with h
    · rw [h, hi₀ j, zero_mul, mul_zero]
    · rfl
  obtain ⟨h, Q₀, hhY, hQ₀, hhYQ⟩ := GlobalTheory.T.integral_right_inverse_normalization k D r (H₂ * (g.val * X₀)) Q₁ (by rw [hH₂Y, hHQ])
  let H := h * H₂
  have hHi₀ : ∀ l, H l i₀ = 0 := fun l => by simp [H, H₂, Matrix.mul_apply]
  obtain ⟨c, hc⟩ := exists_bound hϖ H
  refine ⟨c + 1, fun m hm C hC => ?_⟩
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hϖlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hCX : ∀ a j, valuation k ((C - X₀) a j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun a j => by
    rw [Matrix.sub_apply]; simpa using hC a j
  have hgCX : ∀ i j, valuation k ((g.val * (C - X₀)) i j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun i j => by
    simpa using val_mul_le (valuation k) hg1 hCX i j
  have hc' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k))⁻¹ ^ c := fun l i => by
    rw [← valuation_inv_pow]; exact hc l i
  have hprod : (valuation k (ϖ : k))⁻¹ ^ c * valuation k (ϖ : k) ^ (c + 1) = valuation k (ϖ : k) := by
    rw [inv_pow, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
  have hEb : ∀ l j, valuation k ((H * (g.val * (C - X₀))) l j) ≤ valuation k (ϖ : k) := fun l j => by
    rw [← hprod]; exact val_mul_le (valuation k) hc' hgCX l j
  have hsplit : g.val * C = g.val * X₀ + g.val * (C - X₀) := by rw [Matrix.mul_sub]; abel
  have hHY : H * (g.val * X₀) = h * (H₂ * (g.val * X₀)) := Matrix.mul_assoc _ _ _
  have hHC : H * (g.val * C) = H * (g.val * X₀) + H * (g.val * (C - X₀)) := by rw [hsplit, Matrix.mul_add]
  have hHCint : ∀ l j, (H * (g.val * C)) l j ∈ 𝒪[k] := fun l j => by
    rw [hHC, Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ((hEb l j).trans hϖlt.le)
    rw [hHY]; exact hhY l j
  have hQ₀' : ∀ j l, valuation k (Q₀ j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ₀ j l)
  set E := H * (g.val * (C - X₀)) * Q₀ with hE
  have hEv : ∀ i j, valuation k (E i j) < 1 := fun i j =>
    lt_of_le_of_lt (by simpa using val_mul_le (valuation k) hEb hQ₀' i j) hϖlt
  have hHCQ : H * (g.val * C) * Q₀ = 1 + E := by
    rw [hHC, Matrix.add_mul, hHY, hhYQ]
  obtain ⟨N, hN, hN1⟩ := exists_int_inv_one_add E hEv
  have hN' : ∀ i j, valuation k (N i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (hN i j)
  have hQint : ∀ j l, (Q₀ * N) j l ∈ 𝒪[k] := fun j l => by
    rw [Valuation.mem_integer_iff]; simpa using val_mul_le (valuation k) hQ₀' hN' j l
  have hHCQ' : H * (g.val * C) * (Q₀ * N) = 1 := by rw [← Matrix.mul_assoc, hHCQ, hN1]
  have hrow : ∀ j, valuation k ((g.val * C) i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k) := fun j => by
    rw [hsplit, Matrix.add_apply, hi₀ j, zero_add]; simpa using hgCX i₀ j
  have hmem := GlobalTheory.T.box_function_twisted_coinvariant_rank k A D ϖ hϖ ν β hν hνϖ i₀ r c m (g.val * C) H (Q₀ * N) hHi₀ hc (by omega)
    hHCint hQint hHCQ' hrow
  obtain ⟨s, hs⟩ := omA_boxFn hg ν β ϖ C m
  have hΦ := boxFn_mem_SB ϖ C (fun _ => m)
  have h1 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    rw [hs]; exact Submodule.smul_mem _ _ hmem
  have h2 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) - boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β :=
    Submodule.mem_sup_right (sub_mem_twistSpan ν β g hΦ)
  simpa using sub_mem h1 h2
end
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_box_function_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  atlas_forward_decl GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan
end

section
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem mem_lowRank_succ_sup_twistSpan_of_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r hr Φ hΦ
  obtain ⟨⟨hlc, hcs⟩, hvan⟩ := hΦ
  classical

  have hSclosed : IsClosed {X : Matrix A D k | Φ X ≠ 0} := by
    have : {X : Matrix A D k | Φ X ≠ 0} = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hlc.isOpen_fiber 0).isClosed_compl
  have hScpt : IsCompact {X : Matrix A D k | Φ X ≠ 0} :=
    hcs.isCompact.of_isClosed_subset hSclosed (fun X hX => subset_tsupport Φ hX)

  let m₀ : Matrix A D k → ℕ := fun X =>
    if h : X.rank = r then Classical.choose (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr) else 0
  have hm₀ : ∀ X : Matrix A D k, ∀ h : X.rank = r, ∀ m ≥ m₀ X, ∀ C ∈ box ϖ X (fun _ => m₀ X),
      boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    intro X h
    have := Classical.choose_spec (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr)
    simpa [m₀, h] using this
  let U : Matrix A D k → Set (Matrix A D k) := fun X =>
    if X.rank ≤ r then box ϖ X (fun _ => m₀ X) else {Y | r + 1 ≤ Y.rank}
  have hU : ∀ X ∈ {X : Matrix A D k | Φ X ≠ 0}, U X ∈ nhds X := by
    intro X _
    by_cases h : X.rank ≤ r
    · simp only [U, h, if_true]
      refine (isClopen_box ϖ X _).isOpen.mem_nhds ?_
      intro i j; simp
    · simp only [U, h, if_false]
      exact (GlobalTheory.T.isOpen_rank_ge k A D (r + 1)).mem_nhds (by simp only [Set.mem_setOf_eq]; omega)
  obtain ⟨t, htS, hcover⟩ := hScpt.elim_nhds_subcover U hU
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.schwartz_bruhat_box_decomposition k A D ϖ hϖ Φ ⟨hlc, hcs⟩
  obtain ⟨s, hdec, hconst⟩ := hm₁ (max m₁ (t.sup m₀)) (le_max_left _ _)
  set m := max m₁ (t.sup m₀) with hm
  rw [hdec]
  refine Submodule.sum_mem _ fun c hc => ?_
  by_cases hex : ∃ X₂ ∈ box ϖ c (fun _ => m), X₂.rank ≤ r
  · obtain ⟨X₂, hX₂, hX₂r⟩ := hex
    by_cases hc0 : Φ c = 0
    · rw [hc0, zero_smul]; exact zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hX₂S : Φ X₂ ≠ 0 := by rw [hconst c hc X₂ hX₂]; exact hc0
    have hX₂eq : X₂.rank = r := by
      by_contra hne
      exact hX₂S (hvan X₂ (lt_of_le_of_ne hX₂r hne))
    obtain ⟨x, hxt, hxU⟩ := Set.mem_iUnion₂.1 (hcover hX₂S)
    have hxS : Φ x ≠ 0 := htS x hxt
    by_cases hxr : x.rank ≤ r
    · simp only [U, hxr, if_true] at hxU
      have hxeq : x.rank = r := by
        by_contra hne
        exact hxS (hvan x (lt_of_le_of_ne hxr hne))
      have hmx : m₀ x ≤ m := le_trans (Finset.le_sup (f := m₀) hxt) (le_max_right _ _)
      rw [← boxFn_eq_of_mem hX₂]
      exact hm₀ x hxeq m hmx X₂ hxU
    · simp only [U, hxr, if_false, Set.mem_setOf_eq] at hxU
      omega
  · push_neg at hex
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_)
    refine ⟨boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
    have hYn : Y ∉ box ϖ c (fun _ => m) := fun hYb => by
      have := hex Y hYb; omega
    simp [boxFn, Set.indicator_of_notMem hYn]

end GlobalTheory.RankCoinv
end

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_filtration_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  atlas_forward_decl GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  intro k _ _ _ _ a d _ ν β _ hν ϖ hϖ hνϖ Φ hΦ
  have key : ∀ r ≤ a, Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ)) ⊔
      GlobalTheory.RankCoinv.twistSpan ν β := by
    intro r hr
    induction r with
    | zero => exact Submodule.mem_sup_left ⟨hΦ, fun Y hY => absurd hY (Nat.not_lt_zero _)⟩
    | succ r ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (ih (by omega))
      have := GlobalTheory.T.low_rank_filtration_step k (Fin a) (Fin d) ϖ hϖ ν β hν hνϖ r (by simpa using hr) x hx
      exact Submodule.add_mem _ this (Submodule.mem_sup_right hy)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (key a le_rfl)
  refine ⟨x, hx.1, fun Y hY => hx.2 Y (lt_of_le_of_ne (by simpa using Y.rank_le_card_height) hY), ?_⟩
  have e : Φ - x = y := by rw [← hxy]; abel
  rw [e]; exact hy
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_rank_deficient_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  first | exact @GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | exact GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan <;> assumption)
end
