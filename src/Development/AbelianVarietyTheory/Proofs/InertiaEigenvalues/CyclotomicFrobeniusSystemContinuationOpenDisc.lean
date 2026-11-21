import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.InvBasis

section Formal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (G : Matrix ι ι K⟦X⟧)

theorem coeff_mul_apply (hγ : constantCoeff (γ X) = 0) (g c : K⟦X⟧) (n : ℕ) :
    coeff n (g * γ c) = ∑ d ∈ Finset.range (n + 1), coeff n (g * γ X ^ d) * coeff d c := by
  obtain ⟨a, ha⟩ := X_dvd_iff.2 hγ
  have hc : c = X ^ (n + 1) * (PowerSeries.mk fun i ↦ coeff (i + (n + 1)) c) +
      ∑ d ∈ Finset.range (n + 1), coeff d c • X ^ d := by
    ext m
    rw [map_add, coeff_X_pow_mul', map_sum]
    simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range, coeff_mk]
    split_ifs with h1 h2 h2
    · omega
    · rw [add_zero, Nat.sub_add_cancel h1]
    · rw [zero_add]
    · omega
  conv_lhs => rw [hc]
  rw [map_add, mul_add, map_add, map_mul γ, map_pow γ, map_sum γ, Finset.mul_sum, map_sum]
  have h0 : ∀ b : K⟦X⟧, coeff n (g * (γ X ^ (n + 1) * b)) = 0 := fun b => by
    rw [ha, mul_pow, show g * (X ^ (n + 1) * a ^ (n + 1) * b) = X ^ (n + 1) * (g * a ^ (n + 1) * b) by ring,
      coeff_X_pow_mul', if_neg (by omega)]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_pow, mul_smul_comm, coeff_smul, smul_eq_mul, mul_comm]

theorem coeff_mul_pow_self (hγ : constantCoeff (γ X) = 0) (g : K⟦X⟧) (n : ℕ) :
    coeff n (g * γ X ^ n) = constantCoeff g * coeff 1 (γ X) ^ n := by
  obtain ⟨a, ha⟩ := X_dvd_iff.2 hγ
  rw [ha, mul_pow, show g * (X ^ n * a ^ n) = X ^ n * (g * a ^ n) by ring, coeff_X_pow_mul',
    if_pos le_rfl, Nat.sub_self, coeff_succ_X_mul]
  simp

theorem coeff_op (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1) (c : ι → K⟦X⟧) (i : ι)
    (n : ℕ) : coeff n (G.mulVec (fun j => γ (c j)) i) = coeff 1 (γ X) ^ n * coeff n (c i) +
      ∑ j, ∑ d ∈ Finset.range n, coeff n (G i j * γ X ^ d) * coeff d (c j) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, coeff_mul_apply γ hγ, Finset.sum_range_succ,
    Finset.sum_add_distrib, coeff_mul_pow_self γ hγ]
  rw [add_comm]
  congr 1
  have : ∀ j, constantCoeff (G i j) = (1 : Matrix ι ι K) i j := fun j => by rw [← hG]; rfl
  simp [this, Matrix.one_apply]

theorem exists_rec {α : Type} (F : (n : ℕ) → (Fin n → α) → α) :
    ∃ f : ℕ → α, ∀ n, f n = F n fun k => f k := by
  refine ⟨fun n => Nat.strongRec (motive := fun _ => α) (fun n ih => F n fun k => ih k k.2) n, fun n => ?_⟩
  exact Nat.strongRec_eq _ n

theorem exists_sol (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1) (c₀ : ι → K) :
    ∃ c : ι → K⟦X⟧, (∀ i, constantCoeff (c i) = c₀ i) ∧ G.mulVec (fun j => γ (c j)) = c := by
  obtain ⟨f, hf⟩ := exists_rec (α := ι → K) fun n p => if n = 0 then c₀ else fun i =>
    (1 - coeff 1 (γ X) ^ n)⁻¹ * ∑ j, ∑ d : Fin n, coeff n (G i j * γ X ^ (d : ℕ)) * p d j
  refine ⟨fun i => PowerSeries.mk fun n => f n i, fun i => ?_, ?_⟩
  · rw [constantCoeff_mk, hf, if_pos rfl]
  · ext i n
    rw [coeff_op γ G hγ hG]
    simp only [coeff_mk]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h := congrFun (hf n) i
      rw [if_neg hn] at h
      have h1 : 1 - coeff 1 (γ X) ^ n ≠ 0 := sub_ne_zero.2 (hu n hn).symm
      simp only [Finset.sum_range]
      rw [eq_inv_mul_iff_mul_eq₀ h1] at h
      rw [← h]; ring

theorem sol_eq_zero (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1) (c : ι → K⟦X⟧) (h0 : ∀ i, constantCoeff (c i) = 0)
    (hc : G.mulVec (fun j => γ (c j)) = c) : c = 0 := by
  have : ∀ n i, coeff n (c i) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using h0 i
      · have h := coeff_op γ G hγ hG c i n
        rw [hc, Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun d hd => by
          rw [ih d (Finset.mem_range.1 hd), mul_zero], add_zero] at h
        by_contra hne
        exact hu n hn (mul_right_cancel₀ hne (h.symm.trans (one_mul _).symm))
  ext i n
  simp [this]

omit [DecidableEq ι] in

theorem apply_C (x : K) : γ (C x) = C x := γ.commutes x

end Formal

section Bound

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (G : Matrix ι ι K⟦X⟧)

theorem norm_sol_le (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hint : ∀ i j n d, ‖coeff n (G i j * γ X ^ d)‖ ≤ 1) (B : ℕ → ℝ) (hB0 : 1 ≤ B 0) (hB : Monotone B)
    (hu : ∀ n, coeff 1 (γ X) ^ (n + 1) ≠ 1)
    (hBu : ∀ n, B n ≤ ‖1 - coeff 1 (γ X) ^ (n + 1)‖ * B (n + 1))
    (c : ι → K⟦X⟧) (h0 : ∀ i, ‖constantCoeff (c i)‖ ≤ 1)
    (hc : G.mulVec (fun j => γ (c j)) = c) (n : ℕ) : ∀ i, ‖coeff n (c i)‖ ≤ B n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases n with _ | n
    · simpa using (h0 i).trans hB0
    · have h := coeff_op γ G hγ hG c i (n + 1)
      rw [hc] at h
      have hBn : 0 ≤ B n := zero_le_one.trans (hB0.trans (hB (Nat.zero_le n)))
      have h2 : ‖(1 - coeff 1 (γ X) ^ (n + 1)) * coeff (n + 1) (c i)‖ ≤ B n := by
        rw [sub_mul, one_mul, sub_eq_of_eq_add' h]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hBn fun j _ =>
          IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hBn fun d hd => ?_
        have hd' := Finset.mem_range.1 hd
        rw [norm_mul]
        calc _ ≤ 1 * B d := mul_le_mul (hint _ _ _ _) (ih d hd' j) (norm_nonneg _) zero_le_one
          _ ≤ B n := by rw [one_mul]; exact hB (by omega)
      rw [norm_mul] at h2
      have h1 : 0 < ‖1 - coeff 1 (γ X) ^ (n + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hu n).symm)
      exact le_of_mul_le_mul_left (h2.trans (hBu n)) h1

end Bound

theorem isUnit_det {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R⟦X⟧)
    (hA : A.map constantCoeff = 1) : IsUnit A.det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_one]
  exact isUnit_one

theorem inv_const {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R⟦X⟧)
    (hA : A.map constantCoeff = 1) : A⁻¹.map constantCoeff = 1 := by
  have := congrArg (fun M : Matrix ι ι R⟦X⟧ => M.map constantCoeff) (A.mul_nonsing_inv (isUnit_det A hA))
  simp only [Matrix.map_mul, hA, one_mul] at this
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_basis {K O : Type} [NormedField K] [IsUltrametricDist K] [CommRing O] {ι : Type} [Fintype ι]
    [DecidableEq ι] (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (φ : O →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (a : O⟦X⟧)
    (ha : γ X = PowerSeries.map φ a) (hγ : constantCoeff (γ X) = 0) (B : ℕ → ℝ) (hB0 : 1 ≤ B 0)
    (hB : Monotone B) (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1)
    (hBu : ∀ n, B n ≤ ‖1 - coeff 1 (γ X) ^ (n + 1)‖ * B (n + 1))
    (G : Matrix ι ι O⟦X⟧) (hG : G.map constantCoeff = 1) :
    ∃ U V : Matrix ι ι K⟦X⟧, U * V = 1 ∧ U.map constantCoeff = 1 ∧
      G.map (PowerSeries.map φ) * U.map γ = U ∧
      (∀ c : ι → K⟦X⟧, (G.map (PowerSeries.map φ)).mulVec (fun i => γ (c i)) = c →
        c = U.mulVec fun i => C (constantCoeff (c i))) ∧
      ∀ i j n, ‖coeff n (U i j)‖ ≤ B n ∧ ‖coeff n (V i j)‖ ≤ B n := by
  have hmap : ∀ H : Matrix ι ι O⟦X⟧, H.map constantCoeff = 1 →
      (H.map (PowerSeries.map φ)).map constantCoeff = 1 := fun H hH => by
    ext i j
    have : constantCoeff (H i j) = (1 : Matrix ι ι O) i j := by rw [← hH]; rfl
    rw [Matrix.map_apply, Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hone : ∀ i j, ‖(1 : Matrix ι ι K) i j‖ ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hbd : ∀ H : Matrix ι ι O⟦X⟧, H.map constantCoeff = 1 → ∀ c : ι → K⟦X⟧,
      (∀ i, ‖constantCoeff (c i)‖ ≤ 1) → (H.map (PowerSeries.map φ)).mulVec (fun j => γ (c j)) = c →
      ∀ n i, ‖coeff n (c i)‖ ≤ B n := fun H hH c h0 hc =>
    norm_sol_le γ _ hγ (hmap H hH) (fun i j n d => by
      rw [ha, Matrix.map_apply, ← map_pow, ← map_mul, coeff_map]; exact hφ _) B hB0 hB
      (fun n => hu _ n.succ_ne_zero) hBu c h0 hc
  choose c hc0 hc using fun k => exists_sol γ _ hγ (hmap G hG) hu fun i => (1 : Matrix ι ι K) i k
  set U : Matrix ι ι K⟦X⟧ := Matrix.of fun i k => c k i with hU
  have hU0 : U.map constantCoeff = 1 := by ext i k; exact hc0 k i
  have hGU : G.map (PowerSeries.map φ) * U.map γ = U := by
    ext1 i k; exact congrFun (hc k) i
  have hUV := U.mul_nonsing_inv (isUnit_det U hU0)
  have hVU := U.nonsing_inv_mul (isUnit_det U hU0)
  refine ⟨U, U⁻¹, hUV, hU0, hGU, fun b hb => ?_, fun i j n => ⟨?_, ?_⟩⟩
  · rw [← sub_eq_zero]
    have hγv : (fun j => γ (U.mulVec (fun i => C (constantCoeff (b i))) j)) =
        (U.map γ).mulVec fun i => C (constantCoeff (b i)) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, apply_C, Matrix.map_apply]
    refine sol_eq_zero γ _ hγ (hmap G hG) hu _ (fun i => ?_) ?_
    · have : ∀ j, constantCoeff (U i j) = (1 : Matrix ι ι K) i j := fun j => by rw [← hU0]; rfl
      simp [Matrix.mulVec, dotProduct, this, Matrix.one_apply]
    · have : (fun j => γ ((b - U.mulVec fun i => C (constantCoeff (b i))) j)) =
          (fun j => γ (b j)) - (U.map γ).mulVec fun i => C (constantCoeff (b i)) := by
        rw [← hγv]; funext j; simp only [Pi.sub_apply, map_sub]
      rw [this, Matrix.mulVec_sub, hb, Matrix.mulVec_mulVec, hGU]
  · exact hbd G hG (c j) (fun i => by rw [hc0]; exact hone _ _) (hc j) n i
  · have hHG : (G⁻¹).map (PowerSeries.map φ) * G.map (PowerSeries.map φ) = 1 := by
      rw [← Matrix.map_mul, G.nonsing_inv_mul (isUnit_det G hG), Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : U⁻¹.map γ * U.map γ = 1 := by
      rw [← Matrix.map_mul, hVU, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : U.map γ = (G⁻¹).map (PowerSeries.map φ) * U := by
      conv_rhs => rw [← hGU, ← mul_assoc, hHG, one_mul]
    have h3 : U⁻¹.map γ * (G⁻¹).map (PowerSeries.map φ) = U⁻¹ := by
      rw [h2, ← mul_assoc] at h1
      rw [← mul_one (_ * _), ← hUV, ← mul_assoc, h1, one_mul]
    refine hbd (G⁻¹).transpose (by rw [Matrix.transpose_map, inv_const G hG, Matrix.transpose_one]) (U⁻¹ i)
      (fun k => ?_) ?_ n j
    · have : constantCoeff (U⁻¹ i k) = (1 : Matrix ι ι K) i k := by rw [← inv_const U hU0]; rfl
      rw [this]; exact hone _ _
    · rw [Matrix.transpose_map, Matrix.mulVec_transpose]
      funext k
      exact congrFun (congrFun h3 i) k

theorem bound_le (l : ℕ) [hl : Fact l.Prime] (s n : ℕ) :
    (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹ ≤ ((l : ℝ) ^ ((s : ℝ) + 1 / ((l : ℝ) - 1))) ^ n := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have h0 : (n.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn : ‖(n.factorial : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n.factorial : ℤ)) := by
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_eq_zpow_neg_valuation h0,
      Padic.valuation_natCast]
  have hv : ((l : ℝ) - 1) * (padicValNat l n.factorial : ℝ) ≤ n := by
    have h := sub_one_mul_padicValNat_factorial (p := l) n
    have h' : (l - 1) * padicValNat l n.factorial ≤ n := h ▸ Nat.sub_le _ _
    have h'' : (((l - 1) * padicValNat l n.factorial : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
    rwa [Nat.cast_mul, Nat.cast_sub hl.out.one_lt.le, Nat.cast_one] at h''
  rw [hn, zpow_neg, inv_inv, zpow_natCast, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le h1.le ?_
  have : (padicValNat l n.factorial : ℝ) ≤ 1 / ((l : ℝ) - 1) * n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
  push_cast
  nlinarith

theorem tendsto_of_le (x : ℕ → ℝ) (h0 : ∀ n, 0 ≤ x n) (b : ℝ) (hb : 0 < b) (hx : ∀ n, x n ≤ b ^ n) (r : ℝ)
    (hr : 0 < r) (hrb : r < b⁻¹) : Filter.Tendsto (fun k : ℕ => x k * r ^ k) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun k => mul_nonneg (h0 k) (by positivity)) (fun k => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := b * r) (by positivity) ?_)
  · rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hx k) (by positivity)
  · rwa [← lt_inv_mul_iff₀ hb, mul_one]

theorem norm_algebraMap (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : ℤ_[l]) :
    ‖algebraMap ℤ_[l] ↥LL.1 x‖ = ‖x‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
  exact PadicAlgCl.norm_extends l (x : ℚ_[l])

end GlobalTheory.Cyc.InvBasis

namespace GlobalTheory.Cyc

open InvBasis

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ G : Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL)), G.map PowerSeries.constantCoeff = 1 → ∃ U V : Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1), U * V = 1 ∧ U.map PowerSeries.constantCoeff = 1 ∧ G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * U.map (act l ↥LL.1 u) = U ∧ (∀ c : Fin r → PowerSeries ↥LL.1, (G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1))).mulVec (fun i => act l ↥LL.1 u (c i)) = c → c = U.mulVec fun i => PowerSeries.C (PowerSeries.constantCoeff (c i))) ∧ ∀ i j, (∀ r : ℝ, 0 < r → r < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i j) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) ∧ (∀ r : ℝ, 0 < r → r < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (V i j) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  intro l hl LL s r u hs h2 hu G hG
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hnorm : ∀ n : ℕ, n ≠ 0 → ‖1 - coeff 1 (act l ↥LL.1 u X) ^ n‖ =
      (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := fun n hn => by
    have h := norm_unit_zpow_sub_one l s u hs h2 hu n (by exact_mod_cast hn)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast] at h
    rw [act_X, coeff_one_cyc, ← h, norm_sub_rev, ← norm_algebraMap l LL, map_sub, map_pow, map_one]
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < ‖(n : ℤ_[l])‖ := fun n hn => norm_pos_iff.2 (by exact_mod_cast hn)
  have hstep : ∀ n : ℕ, (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹ =
      (l : ℝ) ^ (-(s : ℤ)) * ‖((n + 1 : ℕ) : ℤ_[l])‖ *
        ((l : ℝ) ^ ((n + 1) * s) * ‖((n + 1).factorial : ℤ_[l])‖⁻¹) := fun n => by
    have := hpos (n + 1) n.succ_ne_zero
    have := hpos _ n.factorial_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, norm_mul, zpow_neg, zpow_natCast]
    field_simp
    ring
  obtain ⟨U, V, hUV, hU0, hGU, huniq, hbd⟩ := exists_basis (act l ↥LL.1 u)
    (algebraMap ↥(OL LL) ↥LL.1) (fun x => (GlobalTheory.Per.Val.mem_OL_iff LL x.1).1 x.2) (cyc l ↥(OL LL) u)
    (by
      rw [act_X, cyc, cyc, map_sub, map_one]
      congr 1)
    (by rw [act_X, cyc_const])
    (fun n => (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹) (by simp)
    (monotone_nat_of_le_succ fun n => by
      have hf := hpos _ (n + 1).factorial_ne_zero
      refine (hstep n).le.trans (mul_le_of_le_one_left (by positivity) ?_)
      exact mul_le_one₀ (zpow_le_one_of_nonpos₀ h1.le (by omega)) (norm_nonneg _) (PadicInt.norm_le_one _))
    (fun n hn h => by
      have h3 := hnorm n hn
      have := hpos n hn
      rw [h, sub_self, norm_zero] at h3
      exact absurd h3 (by positivity))
    (fun n => by rw [hnorm _ n.succ_ne_zero]; exact (hstep n).le) G hG
  refine ⟨U, V, hUV, hU0, hGU, huniq, fun i j => ⟨fun ρ h0 hρ => ?_, fun ρ h0 hρ => ?_⟩⟩
  · rw [Real.rpow_neg (by positivity)] at hρ
    exact tendsto_of_le _ (fun _ => norm_nonneg _) _ (by positivity)
      (fun n => (hbd i j n).1.trans (bound_le l s n)) ρ h0 hρ
  · rw [Real.rpow_neg (by positivity)] at hρ
    exact tendsto_of_le _ (fun _ => norm_nonneg _) _ (by positivity)
      (fun n => (hbd i j n).2.trans (bound_le l s n)) ρ h0 hρ

end GlobalTheory.Cyc
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.Cont

section Bound

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def Bd (r c : ℝ) (a : K⟦X⟧) : Prop := ∀ k, ‖coeff k a‖ * r ^ k ≤ c

omit [IsUltrametricDist K] in
theorem Bd.nonneg {r c : ℝ} {a : K⟦X⟧} (h : Bd r c a) : 0 ≤ c :=
  le_trans (by simp) (h 0)

omit [IsUltrametricDist K] in
theorem Bd.mono {r c c' : ℝ} {a : K⟦X⟧} (h : Bd r c a) (hc : c ≤ c') : Bd r c' a :=
  fun k => (h k).trans hc

omit [IsUltrametricDist K] in
theorem Bd.radius {r r' c : ℝ} {a : K⟦X⟧} (h : Bd r c a) (h0 : 0 ≤ r') (hr : r' ≤ r) : Bd r' c a :=
  fun k => le_trans (by gcongr) (h k)

theorem norm_sum_mul_le {ι : Type} (s : Finset ι) (f : ι → K) {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, ‖f i‖ * x ≤ c) : ‖∑ i ∈ s, f i‖ * x ≤ c := by
  rw [← le_div_iff₀ hx]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    fun i hi => (le_div_iff₀ hx).2 (h i hi)

theorem Bd.sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, Bd r c (f i)) : Bd r c (∑ i ∈ s, f i) := fun k => by
  rw [map_sum]
  exact norm_sum_mul_le _ _ (by positivity) hc fun i hi => h i hi k

theorem Bd.add {r c : ℝ} (hr : 0 < r) {a b : K⟦X⟧} (ha : Bd r c a) (hb : Bd r c b) : Bd r c (a + b) := by
  have := Bd.sum Finset.univ ![a, b] hr ha.nonneg (fun i _ => by fin_cases i <;> assumption)
  simpa using this

theorem Bd.mul {r c c' : ℝ} (hr : 0 < r) {a b : K⟦X⟧} (ha : Bd r c a) (hb : Bd r c' b) :
    Bd r (c * c') (a * b) := fun k => by
  rw [coeff_mul]
  refine norm_sum_mul_le _ _ (by positivity) (mul_nonneg ha.nonneg hb.nonneg) fun p hp => ?_
  have hp' : p.1 + p.2 = k := by simpa using hp
  rw [← hp', norm_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul (ha _) (hb _) (by positivity) ha.nonneg

omit [IsUltrametricDist K] in
theorem bd_C (r : ℝ) (x : K) : Bd r ‖x‖ (C x) := fun k => by
  rw [coeff_C]
  split_ifs with h
  · simp [h]
  · simp

omit [IsUltrametricDist K] in
theorem bd_X {r : ℝ} (hr : 0 < r) : Bd r r (X : K⟦X⟧) := fun k => by
  rw [coeff_X]
  split_ifs with h
  · simp [h]
  · simp [hr.le]

theorem Bd.pow {r c : ℝ} (hr : 0 < r) {a : K⟦X⟧} (ha : Bd r c a) (n : ℕ) : Bd r (c ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using bd_C r (1 : K)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hr ha

omit [IsUltrametricDist K] in
theorem bd_map {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) {r : ℝ} (hr : 0 < r)
    (h1 : r ≤ 1) (a : O⟦X⟧) : Bd r 1 (PowerSeries.map f a) := fun k => by
  rw [coeff_map]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ hr.le h1)

theorem Bd.apply (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (hγ : constantCoeff (γ X) = 0) {r r₁ c : ℝ} (hr : 0 < r)
    (h : Bd r r₁ (γ X)) {a : K⟦X⟧} (ha : Bd r₁ c a) : Bd r c (γ a) := fun k => by
  have := InvBasis.coeff_mul_apply γ hγ 1 a k
  simp only [one_mul] at this
  rw [this]
  refine norm_sum_mul_le _ _ (by positivity) ha.nonneg fun d _ => ?_
  rw [norm_mul, mul_right_comm, mul_comm]
  exact (mul_le_mul_of_nonneg_left (h.pow hr d k) (norm_nonneg _)).trans (ha d)

theorem exists_bd_uniform {ι : Type} [Finite ι] {r : ℝ} (f : ι → K⟦X⟧) (h : ∀ i, ∃ c, Bd r c (f i)) :
    ∃ c, 0 ≤ c ∧ ∀ i, Bd r c (f i) := by
  choose c hc using h
  obtain ⟨B, hB⟩ := (Set.finite_range c).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun i => (hc i).mono ((hB ⟨i, rfl⟩).trans (le_max_left _ _))⟩

omit [IsUltrametricDist K] in
theorem bd_of_tendsto {r : ℝ} {a : K⟦X⟧}
    (h : Filter.Tendsto (fun k : ℕ => ‖coeff k a‖ * r ^ k) Filter.atTop (nhds 0)) : ∃ c, Bd r c a := by
  obtain ⟨c, hc⟩ := h.bddAbove_range
  exact ⟨c, fun k => hc ⟨k, rfl⟩⟩

omit [IsUltrametricDist K] in
theorem Bd.tendsto {r r' c : ℝ} {a : K⟦X⟧} (h : Bd r c a) (h0 : 0 < r') (hr : r' < r) :
    Filter.Tendsto (fun k : ℕ => ‖coeff k a‖ * r' ^ k) Filter.atTop (nhds 0) := by
  have hr0 : 0 < r := h0.trans hr
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := r' / r) (by positivity)
    ((div_lt_one hr0).2 hr)).const_mul c
  rw [mul_zero] at h1
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) h1
  calc ‖coeff k a‖ * r' ^ k = ‖coeff k a‖ * r ^ k * (r' / r) ^ k := by
        rw [div_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (h k) (by positivity)

theorem ex_mul {r : ℝ} (hr : 0 < r) {a b : K⟦X⟧} (ha : ∃ c, Bd r c a) (hb : ∃ c, Bd r c b) :
    ∃ c, Bd r c (a * b) := by
  obtain ⟨c, ha⟩ := ha
  obtain ⟨c', hb⟩ := hb
  exact ⟨_, ha.mul hr hb⟩

theorem ex_sum {κ : Type} [Fintype κ] {r : ℝ} (hr : 0 < r) (f : κ → K⟦X⟧) (h : ∀ i, ∃ c, Bd r c (f i)) :
    ∃ c, Bd r c (∑ i, f i) := by
  obtain ⟨c, h0, hc⟩ := exists_bd_uniform f h
  exact ⟨c, Bd.sum _ _ hr h0 fun i _ => hc i⟩

theorem continuation_abstract {ι κ : Type} [Fintype κ] (γ : K⟦X⟧ →ₐ[K] K⟦X⟧)
    (hγ : constantCoeff (γ X) = 0) (lam : ℝ) (hlam : lam < 1)
    (hγb : ∀ r, 0 < r → r < 1 → Bd r (max lam r * r) (γ X)) (σ : ι → ι)
    (W P D : ι → Matrix κ κ K⟦X⟧) (hP : ∀ r, 0 < r → r < 1 → ∀ i a b, ∃ c, Bd r c (P i a b))
    (hD : ∀ r, 0 < r → r < 1 → ∀ i a b, ∃ c, Bd r c (D i a b))
    (hW : ∀ i, W i = P i * (W (σ i)).map γ * D i) (ρ : ℝ) (hρ : 0 < ρ)
    (h : ∀ i a b, ∃ c, Bd ρ c (W i a b)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∀ i a b, ∃ c, Bd r c (W i a b) := by
  set q := max lam r with hq
  have hq0 : 0 < q := lt_max_of_lt_right hr
  have hq1 : q < 1 := max_lt hlam hr1
  have step : ∀ x, 0 < x → x ≤ r → (∀ i a b, ∃ c, Bd (q * x) c (W i a b)) →
      ∀ i a b, ∃ c, Bd x c (W i a b) := by
    intro x hx hxr hb i a b
    have hx1 : x < 1 := hxr.trans_lt hr1
    have hγx : Bd x (q * x) (γ X) :=
      (hγb x hx hx1).mono (mul_le_mul_of_nonneg_right (max_le_max le_rfl hxr) hx.le)
    rw [hW i, Matrix.mul_apply]
    refine ex_sum hx _ fun j => ex_mul hx ?_ (hD x hx hx1 _ _ _)
    rw [Matrix.mul_apply]
    refine ex_sum hx _ fun k => ex_mul hx (hP x hx hx1 _ _ _) ?_
    obtain ⟨c, hc⟩ := hb (σ i) k j
    exact ⟨c, Bd.apply γ hγ hx hγx hc⟩
  have iter : ∀ n : ℕ, (∀ i a b, ∃ c, Bd (q ^ n * r) c (W i a b)) → ∀ i a b, ∃ c, Bd r c (W i a b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hb
      refine ih (step _ (by positivity) (mul_le_of_le_one_left hr.le (pow_le_one₀ hq0.le hq1.le)) ?_)
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hρ hq1
  refine iter n fun i a b => ?_
  obtain ⟨c, hc⟩ := h i a b
  exact ⟨c, hc.radius (by positivity) ((mul_le_of_le_one_right (by positivity) hr1.le).trans hn.le)⟩

end Bound

variable (l : ℕ) [hl : Fact l.Prime]

theorem phi_X (O : Type) [CommRing O] [Algebra ℤ_[l] O] : phi l O X = (1 + X : O⟦X⟧) ^ l - 1 :=
  act_nat_X l O l

theorem phi_log_series (K : Type) [Field K] [CharZero K] [Algebra ℤ_[l] K] (t : K⟦X⟧)
    (h0 : constantCoeff t = 0) (h1 : (1 + X) * derivative K t = 1) : phi l K t = (l : K⟦X⟧) * t := by
  have hs : HasSubst (cyc l K (l : ℤ_[l])) := HasSubst.of_constantCoeff_zero' (cyc_const l K _)
  have hne : (1 + X : K⟦X⟧) ≠ 0 := fun h => by simp [h] at h1
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.out.one_le
  apply derivative.ext
  · have e : derivative K (phi l K t) = phi l K (derivative K t) * derivative K ((1 + X) ^ l - 1) := by
      rw [phi, act_apply, act_apply, derivative_subst hs, cyc_natCast]
    have e2 := congrArg (phi l K) h1
    rw [map_mul, map_add, map_one, phi_X, add_sub_cancel] at e2
    have e3 : derivative K ((1 + X : K⟦X⟧) ^ l - 1) = (l : K⟦X⟧) * (1 + X : K⟦X⟧) ^ (l - 1) := by
      simp [Derivation.leibniz_pow]
    have e4 : derivative K ((l : K⟦X⟧) * t) = (l : K⟦X⟧) * derivative K t := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    apply mul_left_cancel₀ hne
    have e5 : (1 + X : K⟦X⟧) ^ l = (1 + X) ^ (l - 1) * (1 + X) := by rw [← pow_succ, hl1]
    rw [e5] at e2
    rw [e, e3, e4]
    linear_combination (l : K⟦X⟧) * e2 - (l : K⟦X⟧) * h1
  · obtain ⟨a, rfl⟩ := X_dvd_iff.2 h0
    simp [phi_X]

theorem inv_le_norm_nat (k : ℕ) (hk : k ≠ 0) : 1 ≤ k * ‖(k : ℤ_[l])‖ := by
  have h1 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have h0 : (k : ℚ_[l]) ≠ 0 := by exact_mod_cast hk
  rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_eq_zpow_neg_valuation h0,
    Padic.valuation_natCast, zpow_neg, zpow_natCast, ← div_eq_mul_inv, one_le_div (by positivity)]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hk) pow_padicValNat_dvd

variable (LL : FinExt l)

theorem norm_nat (k : ℕ) : ‖(k : ↥LL.1)‖ = ‖(k : ℤ_[l])‖ := by
  rw [← InvBasis.norm_algebraMap l LL, map_natCast]

theorem bd_log_div (a : (↥LL.1)⟦X⟧) (h1 : (1 + X) * derivative _ (X * a) = 1) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : ∃ c, Bd r c a := by
  have hd : ∀ k, ‖coeff k (derivative _ (X * a))‖ = 1 := by
    intro k
    induction k with
    | zero =>
      have := congrArg (coeff 0) h1
      rw [add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero, coeff_one, if_pos rfl] at this
      rw [this, norm_one]
    | succ k ih =>
      have := congrArg (coeff (k + 1)) h1
      rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_one, if_neg k.succ_ne_zero] at this
      rw [eq_neg_of_add_eq_zero_left this, norm_neg, ih]
  have hb : ∀ k, ‖coeff k a‖ ≤ k + 1 := by
    intro k
    have h := hd k
    rw [coeff_derivative, coeff_succ_X_mul, norm_mul, ← Nat.cast_succ, norm_nat] at h
    have h2 := inv_le_norm_nat l (k + 1) k.succ_ne_zero
    calc ‖coeff k a‖ ≤ ‖coeff k a‖ * (((k + 1 : ℕ) : ℝ) * ‖((k + 1 : ℕ) : ℤ_[l])‖) :=
          le_mul_of_one_le_right (norm_nonneg _) h2
      _ = k + 1 := by rw [mul_left_comm, h]; simp
  refine bd_of_tendsto (squeeze_zero (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_right (hb k) (by positivity)) ?_)
  simpa [add_mul] using (tendsto_self_mul_const_pow_of_lt_one hr.le hr1).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)

theorem norm_OL (x : ↥(OL LL)) : ‖algebraMap ↥(OL LL) ↥LL.1 x‖ ≤ 1 :=
  (GlobalTheory.Per.Val.mem_OL_iff LL x.1).1 x.2

theorem bd_phi_X (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Bd r (max (l : ℝ)⁻¹ r * r) (phi l ↥LL.1 X) := by
  obtain ⟨b, hb⟩ := exists_add_pow_prime_eq hl.out (X : (↥(OL LL))⟦X⟧) 1
  have e : phi l ↥LL.1 X = X ^ l + C (l : ↥LL.1) * X *
      PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) b := by
    have := congrArg (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) hb
    simp only [map_add, map_pow, map_mul, map_one, map_X, map_natCast] at this
    rw [phi_X, map_natCast, add_comm 1 X, this]
    ring
  rw [e]
  refine Bd.add hr (((bd_X hr).pow hr l).mono ?_)
    (((((bd_C r _).mul hr (bd_X hr))).mul hr (bd_map _ (norm_OL l LL) hr hr1.le b)).mono ?_)
  · calc r ^ l ≤ r ^ 2 := pow_le_pow_of_le_one hr.le hr1.le hl.out.two_le
      _ = r * r := sq r
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le
  · rw [mul_one, norm_nat, PadicInt.norm_p]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le

theorem phi_X_const (O : Type) [CommRing O] [Algebra ℤ_[l] O] : constantCoeff (phi l O X) = 0 := by
  simp [phi_X]

theorem inv_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

theorem ex_phi_pow (j : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {a : (↥LL.1)⟦X⟧} (ha : ∃ c, Bd r c a) :
    ∃ c, Bd r c ((phi l ↥LL.1 ^ j) a) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    rw [pow_succ', AlgHom.mul_apply]
    exact ⟨c, Bd.apply _ (phi_X_const l _) hr ((bd_phi_X l LL r hr hr1).mono
      (mul_le_of_le_one_left hr.le (max_le (inv_lt_one l).le hr1.le))) hc⟩

theorem bd_tau (s : ℕ) (t τ : (↥LL.1)⟦X⟧) (h0 : constantCoeff t = 0)
    (h1 : (1 + X) * derivative _ t = 1) (hτ : XX l ↥LL.1 s * τ = t) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ c, Bd r c τ := by
  have hj : ∀ j : ℕ, (phi l ↥LL.1 ^ j) t = (l : (↥LL.1)⟦X⟧) ^ j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, map_mul, map_pow, map_natCast, phi_log_series l _ t h0 h1]
      ring
  have hX : XX l ↥LL.1 s ≠ 0 := fun h => by
    rw [h, zero_mul] at hτ
    simp [← hτ] at h1
  obtain ⟨a, ha⟩ := X_dvd_iff.2 h0
  have h2 := hj (s - 1)
  conv_lhs at h2 => rw [ha, map_mul, phi_pow_X]
  have h3 : (phi l ↥LL.1 ^ (s - 1)) a = (l : (↥LL.1)⟦X⟧) ^ (s - 1) * τ := by
    apply mul_left_cancel₀ hX
    rw [mul_left_comm, hτ, ← h2, XX]
  have hl0 : (l : ↥LL.1) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have h4 : τ = C (((l : ↥LL.1) ^ (s - 1))⁻¹) * (phi l ↥LL.1 ^ (s - 1)) a := by
    rw [h3, ← mul_assoc, ← map_natCast (C (R := ↥LL.1)), ← map_pow, ← map_mul,
      inv_mul_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
  rw [h4]
  exact ex_mul hr ⟨_, bd_C r _⟩ (ex_phi_pow l LL _ hr hr1 (bd_log_div l LL a (ha ▸ h1) r hr hr1))

end GlobalTheory.Cyc.Cont

namespace GlobalTheory.Cyc

open Cont

theorem continuation_to_open_disc : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r n M : ℕ) [NeZero n], 1 ≤ s → ∀ (t τ : PowerSeries ↥LL.1), PowerSeries.constantCoeff t = 0 → (1 + PowerSeries.X) * PowerSeries.derivative ↥LL.1 t = 1 → XX l ↥LL.1 s * τ = t → ∀ (U : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1)) (Pm : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL))) (Cm : ZMod n → Matrix (Fin r) (Fin r) ↥LL.1) (ρ : ℝ), 0 < ρ → (∀ i, QQ l ↥LL.1 s ^ M • U i = (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * (U (i - 1)).map (phi l ↥LL.1) * (Cm i).map PowerSeries.C) → (∀ i a b, (∀ r : ℝ, 0 < r → r < ρ → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0))) → ∀ i a b, (∀ r : ℝ, 0 < r → r < 1 → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (τ ^ M * U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  intro l hl LL s r n M _ hs t τ h0 h1 hτ U Pm Cm ρ hρ hU hc i a b x hx hx1
  have hX : XX l ↥LL.1 s ≠ 0 := fun h => by
    rw [h, zero_mul] at hτ
    simp [← hτ] at h1
  have hQ : QQ l ↥LL.1 s * phi l ↥LL.1 τ = (l : (↥LL.1)⟦X⟧) * τ := by
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← (XX_QQ_properties l _ s hs).1, ← map_mul, hτ, phi_log_series l _ t h0 h1, ← hτ]
    ring
  have hl0 : (l : ↥LL.1) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hinv : C (((l : ↥LL.1) ^ M)⁻¹) * (l : (↥LL.1)⟦X⟧) ^ M = 1 := by
    rw [← map_natCast (C (R := ↥LL.1)), ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hl0), map_one]
  obtain ⟨y, hxy, hy1⟩ := exists_between hx1
  have key := continuation_abstract (phi l ↥LL.1) (phi_X_const l _) _ (inv_lt_one l) (bd_phi_X l LL)
    (fun i : ZMod n => i - 1) (fun i => τ ^ M • U i)
    (fun i => (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)))
    (fun i => C (((l : ↥LL.1) ^ M)⁻¹) • (Cm i).map C)
    (fun z hz hz1 i a b => ⟨1, bd_map _ (norm_OL l LL) hz hz1.le _⟩)
    (fun z hz hz1 i a b => ex_mul hz ⟨_, bd_C z _⟩ ⟨_, bd_C z _⟩)
    (fun i => by
      have e : (τ ^ M • U (i - 1)).map (phi l ↥LL.1) =
          phi l ↥LL.1 τ ^ M • (U (i - 1)).map (phi l ↥LL.1) := by
        ext1 a b
        simp
      simp only [e, Matrix.mul_smul, Matrix.smul_mul, ← hU, smul_smul]
      congr 1
      have : phi l ↥LL.1 τ ^ M * QQ l ↥LL.1 s ^ M = (l : (↥LL.1)⟦X⟧) ^ M * τ ^ M := by
        rw [← mul_pow, mul_comm, hQ, mul_pow]
      linear_combination -(C (((l : ↥LL.1) ^ M)⁻¹)) * this - τ ^ M * hinv)
    (min (ρ / 2) (1 / 2)) (by positivity)
    (fun i a b => by
      have hz : 0 < min (ρ / 2) (1 / 2) := by positivity
      obtain ⟨c, hc'⟩ := bd_tau l LL s t τ h0 h1 hτ _ hz ((min_le_right _ _).trans_lt (by norm_num))
      exact ex_mul hz ⟨_, hc'.pow hz M⟩
        (bd_of_tendsto (hc i a b _ hz ((min_le_left _ _).trans_lt (by linarith)))))
    y (hx.trans hxy) hy1 i a b
  obtain ⟨c, hc⟩ := key
  exact hc.tendsto hx hxy

end GlobalTheory.Cyc
end
end
