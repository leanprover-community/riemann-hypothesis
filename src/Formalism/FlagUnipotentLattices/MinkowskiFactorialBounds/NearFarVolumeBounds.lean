import Formalism.FlagUnipotentLattices.CoveringRadius2
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds

open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

namespace Formalism.HermitianLatticeCounting.P

open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)

lemma hs_sq_trace_b {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show star (Y b a) = (starRingEnd ℂ) (Y b a) from rfl, Complex.conj_mul']

lemma hs_unitary_conj_b {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℂ) (hk : kᴴ * k = 1) :
    hs (k * X * kᴴ) = hs X := by
  unfold hs
  congr 1
  have : ((∑ a, ∑ b, ‖(k * X * kᴴ) a b‖ ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs_sq_trace_b, hs_sq_trace_b]
    have e : (k * X * kᴴ)ᴴ * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
    rw [e, trace_mul_cycle, hk, Matrix.one_mul]
  exact_mod_cast this

lemma hs_neg_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : hs (-X) = hs X := by
  simp [hs]

lemma eigenvalue_le_hs_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (i : Fin N) :
    hX.eigenvalues i ≤ hs X := by
  unfold hs
  rw [← Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues X hX]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun j => hX.eigenvalues j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

lemma exp_sq_psd_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X).PosSemidef := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Fin N → ℂ := RCLike.ofReal ∘ hX.eigenvalues with hDdef
  have hUU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hspec : X = U * diagonal D * Uᴴ := by
    conv_lhs => rw [hX.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU, hUU'⟩, rfl⟩
  have hexp : NormedSpace.exp X = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec, ← hinv, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal]
    have hD : NormedSpace.exp D = fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ) := by
      funext i
      rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
      rfl
    rw [hD, hinv]
  have e : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X)
      = U * diagonal (fun i => ((Real.exp (hs X) ^ 2 - Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hexp]
    have e1 : U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ *
        (U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ)
        = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
        diagonal_mul_diagonal]
      congr 3
      ext i
      push_cast; ring
    have e2 : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ))
        = U * diagonal (fun _ => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      have : diagonal (fun _ : Fin N => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ))
          = ((Real.exp (hs X) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
        ext a b; simp [diagonal_apply, one_apply]
      rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
      ext a b; simp
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3
    ext i
    push_cast; ring
  rw [e]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  rw [Complex.zero_le_real, sub_nonneg]
  gcongr
  exact eigenvalue_le_hs_b X hX i

theorem polar_decomposition_inverse : PolarInv := by
  intro N k X hk hX
  have hk1 : k * kᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.1 hk)
  have hk2 : kᴴ * k = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 hk)
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv hk1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, hk1, hk2⟩, rfl⟩
  have hexp : NormedSpace.exp (-(k * X * kᴴ)) = k * (NormedSpace.exp X)⁻¹ * kᴴ := by
    have : -(k * X * kᴴ) = k * (-X) * k⁻¹ := by rw [hinv]; simp
    rw [this, Matrix.exp_conj k _ hunit, Matrix.exp_neg, hinv]
  have hdet : IsUnit (NormedSpace.exp X).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.inv_eq_right_inv
    rw [hexp]
    calc k * NormedSpace.exp X * (kᴴ * (k * (NormedSpace.exp X)⁻¹ * kᴴ))
        = k * (NormedSpace.exp X * ((kᴴ * k) * (NormedSpace.exp X)⁻¹)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk2, Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, hk1]
  · exact (Matrix.isHermitian_mul_mul_conjTranspose k hX).neg
  · rw [hs_neg_b, hs_unitary_conj_b k X hk2]
  · have e : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp X * NormedSpace.exp X := by
      rw [conjTranspose_mul, (hX.exp).eq]
      calc NormedSpace.exp X * kᴴ * (k * NormedSpace.exp X)
          = NormedSpace.exp X * ((kᴴ * k) * NormedSpace.exp X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hk2, Matrix.one_mul]
    rw [e]
    exact exp_sq_psd_b X hX

open Classical in

lemma layer_sum_b (ι Γ : Type) [Fintype ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B K : ℝ)
    (F : ℝ → ℝ) (u w : ℕ → ℝ) (hA : 0 ≤ A) (hu : ∀ i, 0 ≤ u i) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ t, 0 ≤ F t) (hlev : ∀ t, 0 ≤ t → ∃ i, t ≤ u i ∧ F t ≤ w i)
    (hd : ∀ γ ∈ S, ∀ v, 0 ≤ d γ v)
    (hcount : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v))
    (hK : ∀ M, ∑ i ∈ range M, w i * Real.exp (B * u i) ≤ K) :
    ∑ γ ∈ S, ∏ v, F (d γ v) ≤ A * K ^ Fintype.card ι := by
  have hlev' : ∀ t : ℝ, ∃ i, 0 ≤ t → (t ≤ u i ∧ F t ≤ w i) := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨i, hi⟩ := hlev t ht
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose lev hl using hlev'
  set L : Γ → ι → ℕ := fun γ v => lev (d γ v) with hL
  set M : ℕ := (S.sup fun γ => univ.sup (L γ)) + 1 with hM
  set T : Finset (ι → ℕ) := Fintype.piFinset fun _ => range M with hT
  have hmaps : ∀ γ ∈ S, L γ ∈ T := by
    intro γ hγ
    rw [hT, Fintype.mem_piFinset]
    intro v
    rw [mem_range, hM, Nat.lt_succ_iff]
    exact le_trans (Finset.le_sup (f := L γ) (mem_univ v))
      (Finset.le_sup (f := fun γ => univ.sup (L γ)) hγ)
  have h1 : ∑ γ ∈ S, ∏ v, F (d γ v) ≤ ∑ γ ∈ S, ∏ v, w (L γ v) := by
    apply Finset.sum_le_sum
    intro γ hγ
    apply Finset.prod_le_prod
    · intro v _; exact hF _
    · intro v _; exact (hl _ (hd γ hγ v)).2
  have h2 : ∑ γ ∈ S, ∏ v, w (L γ v) = ∑ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h3 : ∀ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) ≤
      A * ∏ v, (w (I v) * Real.exp (B * u (I v))) := by
    intro I _
    have e1 : ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) = ((S.filter fun γ => L γ = I).card : ℝ) * ∏ v, w (I v) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [(Finset.mem_filter.1 hγ).2]
    rw [e1]
    have hsub : (S.filter fun γ => L γ = I) ⊆ (S.filter fun γ => ∀ v, d γ v ≤ u (I v)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ ⊢
      refine ⟨hγ.1, fun v => ?_⟩
      rw [← hγ.2]
      exact (hl _ (hd γ hγ.1 v)).1
    have hc : ((S.filter fun γ => L γ = I).card : ℝ) ≤ A * Real.exp (B * ∑ v, u (I v)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (hcount _ fun v => hu _)
    have hp : 0 ≤ ∏ v, w (I v) := Finset.prod_nonneg fun v _ => hw _
    calc _ ≤ A * Real.exp (B * ∑ v, u (I v)) * ∏ v, w (I v) := mul_le_mul_of_nonneg_right hc hp
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]; ring
  have h4 : ∑ I ∈ T, A * ∏ v, (w (I v) * Real.exp (B * u (I v))) =
      A * (∑ i ∈ range M, w i * Real.exp (B * u i)) ^ Fintype.card ι := by
    have := Finset.prod_univ_sum (fun _ : ι => range M) (fun _ i => w i * Real.exp (B * u i))
    rw [← Finset.mul_sum, hT, ← this, Finset.prod_const, Finset.card_univ]
  have h5 : 0 ≤ ∑ i ∈ range M, w i * Real.exp (B * u i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := Finset.sum_le_sum h3
    _ = _ := h4
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact pow_le_pow_left₀ h5 (hK M) _

lemma geom_partial_le_b (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ i ∈ range M, x ^ i ≤ 1 / (1 - x) := by
  rw [one_div, ← tsum_geometric_of_lt_one hx0 hx1]
  exact (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)

theorem all_sum_rate : AllSumRate := by
  intro ι Γ _ _ S d A B h q hq hA hB hh hd hcount
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : 1 ≤ Real.sqrt (2 * (q:ℝ)) := by
    rw [Real.one_le_sqrt]; linarith
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := by linarith
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hx1 : Real.exp (-B) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  refine layer_sum_b ι Γ S d A B _ (fun t => Real.exp (-(decExp h q t))) (fun i => (i:ℝ) + 1)
    (fun i => Real.exp (-(2 * B * i))) hA (fun i => by positivity) (fun i => (Real.exp_pos _).le)
    (fun t => (Real.exp_pos _).le) ?_ hd hcount ?_
  · intro t ht
    refine ⟨⌈t⌉₊ - 1, ?_, ?_⟩
    · have h1 := Nat.le_ceil t
      have h2 : (⌈t⌉₊ : ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) + 1 := by
        have : ⌈t⌉₊ ≤ (⌈t⌉₊ - 1) + 1 := by omega
        exact_mod_cast this
      linarith
    · rw [Real.exp_le_exp, neg_le_neg_iff]
      unfold decExp
      rcases Nat.eq_zero_or_pos (⌈t⌉₊ - 1) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, mul_zero]
        have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := le_min (by positivity) (by positivity)
        positivity
      · have hlt : ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t := by
          rw [← Nat.lt_ceil]; omega
        have hi1 : (1:ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h0
        set i : ℝ := ((⌈t⌉₊ - 1 : ℕ) : ℝ) with hi
        have ht1 : 1 ≤ t := by linarith
        have hmin : i / Real.sqrt (2 * (q:ℝ)) ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := by
          apply le_min
          · calc i / Real.sqrt (2 * (q:ℝ)) ≤ i := div_le_self (by linarith) hs1
              _ ≤ t ^ 2 := by nlinarith
          · gcongr
        calc 2 * B * i = (16 * B * Real.sqrt (2 * (q:ℝ))) / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by
              field_simp; ring
          _ ≤ h / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by gcongr
          _ ≤ _ := by gcongr
  · intro M
    have e : ∀ i : ℕ, Real.exp (-(2 * B * i)) * Real.exp (B * ((i:ℝ) + 1)) = Real.exp B * Real.exp (-B) ^ i := by
      intro i
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    simp_rw [e]
    rw [← Finset.mul_sum, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (geom_partial_le_b _ (Real.exp_pos _).le hx1 M) (Real.exp_pos _).le





open scoped ENNReal





section Dedekind

open Ideal UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

noncomputable def normWeight_b (K : Type) [Field K] [NumberField K] (i : ℕ) : Ideal (𝓞 K) →* ℝ where
  toFun I := ((absNorm I : ℝ)⁻¹) ^ i
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul, mul_inv, mul_pow]

end Dedekind

end Formalism.HermitianLatticeCounting.P
