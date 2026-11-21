import Mathlib
import GroundTheory.AutomorphicForms.GL2.IsAddHaarMeasureMatrixMeasureFinSq
import GroundTheory.AutomorphicForms.CompactModCentre

section
noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Measure Polynomial ValuativeRel
open scoped NNReal ENNReal

theorem hasSum_geom_poly {β : ℂ} (hβ : β ≠ 0) (e : ℕ) {P : ℤ → ℂ[X]} {j₀ j₁ : ℤ} (hj : j₀ ≤ j₁)
    (h0 : ∀ j < j₀, P j = 0) (h1 : ∀ j ≥ j₁, P j = P j₁) :
    ∃ (Pn : ℂ[X]) (N : ℕ), ∀ x : ℂ, x ≠ 0 → ‖β * x ^ e‖ < 1 →
      HasSum (fun j : ℤ => (β * x ^ e) ^ j * (P j).eval x)
        (Pn.eval x / (x ^ N * (1 - β * x ^ e))) := by
  classical
  set N : ℕ := e * (-j₀).toNat with hN
  have hNj : ∀ j, j₀ ≤ j → (0 : ℤ) ≤ (N : ℤ) + e * j := by
    intro j hj'
    have : (-j₀ : ℤ) ≤ ((-j₀).toNat : ℤ) := Int.self_le_toNat _
    have he : (0 : ℤ) ≤ e := Int.natCast_nonneg e
    push_cast [hN]
    nlinarith
  set S : Finset ℤ := Finset.Ico j₀ j₁
  set Pn : ℂ[X] := (1 - C β * X ^ e) * ∑ j ∈ S, C (β ^ j) * X ^ ((N : ℤ) + e * j).toNat * P j +
    C (β ^ j₁) * X ^ ((N : ℤ) + e * j₁).toNat * P j₁ with hPn
  refine ⟨Pn, N, fun x hx hlt => ?_⟩
  have hne : (1 : ℂ) - β * x ^ e ≠ 0 := by
    intro h
    have : β * x ^ e = 1 := by linear_combination -h
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hxN : x ^ N ≠ 0 := pow_ne_zero _ hx

  have hpow : ∀ j, j₀ ≤ j → (β * x ^ e) ^ j * x ^ N = β ^ j * x ^ ((N : ℤ) + e * j).toNat := by
    intro j hj'
    rw [mul_zpow, ← zpow_natCast x ((N : ℤ) + e * j).toNat, Int.toNat_of_nonneg (hNj j hj'),
      zpow_add₀ hx, zpow_natCast, ← zpow_natCast x e, ← _root_.zpow_mul]
    ring

  set f : ℤ → ℂ := fun j => (β * x ^ e) ^ j * (P j).eval x
  have hfin : HasSum (fun j => if j < j₁ then f j else 0) (∑ j ∈ S, f j) := by
    have h : HasSum (fun j : ℤ => if j < j₁ then f j else 0)
        (∑ j ∈ S, (if j < j₁ then f j else 0)) := hasSum_sum_of_ne_finset_zero fun j hj => ?_
    · convert h using 1
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [S, Finset.mem_Ico] at hj
      simp [hj.2]
    · simp only [S, Finset.mem_Ico, not_and_or, not_le] at hj
      split_ifs with h
      · rcases hj with hj | hj
        · simp [f, h0 j hj]
        · exact absurd h hj
      · rfl
  have hz : β * x ^ e ≠ 0 := mul_ne_zero hβ (pow_ne_zero _ hx)
  have htail : HasSum (fun j => if j < j₁ then 0 else f j)
      ((β * x ^ e) ^ j₁ * (P j₁).eval x * (1 - β * x ^ e)⁻¹) := by
    have hg : HasSum (fun k : ℕ => (β * x ^ e) ^ j₁ * (P j₁).eval x * (β * x ^ e) ^ k)
        ((β * x ^ e) ^ j₁ * (P j₁).eval x * (1 - β * x ^ e)⁻¹) :=
      (hasSum_geometric_of_norm_lt_one hlt).mul_left _
    have hinj : Function.Injective (fun k : ℕ => j₁ + (k : ℤ)) := fun a b h => by
      simpa using h
    rw [← hinj.hasSum_iff fun j hj => ?_]
    · convert hg using 1
      funext k
      simp only [Function.comp_apply, f]
      rw [if_neg (by omega), h1 _ (by omega), zpow_add₀ hz, zpow_natCast]
      ring
    · split_ifs with h
      · rfl
      · exact absurd ⟨(j - j₁).toNat, by simp; omega⟩ hj
  have htot := hfin.add htail
  have hf : (fun j => (if j < j₁ then f j else 0) + (if j < j₁ then 0 else f j)) = f := by
    funext j; split_ifs <;> simp
  rw [hf] at htot
  convert htot using 1
  rw [div_eq_iff (mul_ne_zero hxN hne)]
  simp only [Pn, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_pow, eval_X, eval_finsetSum]
  have hS : ∀ j ∈ S, β ^ j * x ^ ((N : ℤ) + e * j).toNat * (P j).eval x =
      f j * x ^ N := fun j hj => by
    simp only [S, Finset.mem_Ico] at hj
    simp only [f]
    rw [← hpow j hj.1]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul, ← hpow j₁ hj]
  field_simp

theorem tsum_int_lt_top_of_le_geom {a : ℤ → ℝ≥0∞} {j₀ : ℤ} {M r : ℝ≥0∞} (hM : M ≠ ∞) (hr : r < 1)
    (h0 : ∀ j < j₀, a j = 0) (h1 : ∀ k : ℕ, a (j₀ + k) ≤ M * r ^ k) : ∑' j, a j < ∞ := by
  have hinj : Function.Injective (fun k : ℕ => j₀ + (k : ℤ)) := fun x y h => by simpa using h
  have hsupp : Function.support a ⊆ Set.range (fun k : ℕ => j₀ + (k : ℤ)) := by
    intro j hj
    by_contra hj'
    apply hj
    refine h0 j ?_
    by_contra hlt
    exact hj' ⟨(j - j₀).toNat, by simp; omega⟩
  rw [← hinj.tsum_eq hsupp]
  calc ∑' k : ℕ, a (j₀ + k) ≤ ∑' k : ℕ, M * r ^ k := ENNReal.tsum_le_tsum h1
    _ = M * (1 - r)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr))

theorem tsum_int_lt_top_of_le_geom₂ {a : ℤ → ℝ≥0∞} {M r₁ r₂ : ℝ≥0∞} (hM : M ≠ ∞) (hr₁ : r₁ < 1)
    (hr₂ : r₂ < 1) (h₁ : ∀ k : ℕ, a k ≤ M * r₁ ^ k) (h₂ : ∀ k : ℕ, a (-(k + 1 : ℤ)) ≤ M * r₂ ^ k) :
    ∑' j, a j < ∞ := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · calc ∑' k : ℕ, a k ≤ ∑' k : ℕ, M * r₁ ^ k := ENNReal.tsum_le_tsum h₁
      _ = M * (1 - r₁)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr₁))
  · calc ∑' k : ℕ, a (-(k + 1 : ℤ)) ≤ ∑' k : ℕ, M * r₂ ^ k := ENNReal.tsum_le_tsum fun k => by
          have := h₂ k
          push_cast at this ⊢
          exact this
      _ = M * (1 - r₂)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr₂))

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

variable (m) in

structure IsCentralCoeff (α : ℂ) (c : GL (Fin m) F → ℂ) : Prop where
  continuous : Continuous c
  ne_zero : α ≠ 0
  mul_left : ∀ g, c (centralUnif F m * g) = α * c g
  support : ∃ C : Set (GL (Fin m) F), IsCompact C ∧
    ∀ g, c g ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C

namespace IsCentralCoeff

variable {α : ℂ} {c : GL (Fin m) F → ℂ}

theorem zpow_mul (hc : IsCentralCoeff m α c) (j : ℤ) (g : GL (Fin m) F) :
    c (centralUnif F m ^ j * g) = α ^ j * c g := by
  induction j using Int.induction_on generalizing g with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, mul_assoc, ih, hc.mul_left, zpow_add_one₀ hc.ne_zero]
    ring
  | pred k ih =>
    have h := hc.mul_left ((centralUnif F m)⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    rw [_root_.zpow_sub_one, mul_assoc, ih, zpow_sub_one₀ hc.ne_zero, h]
    field_simp [hc.ne_zero]

theorem inv (hc : IsCentralCoeff m α c) : IsCentralCoeff m α⁻¹ (fun g => c g⁻¹) := by
  refine ⟨hc.continuous.comp continuous_inv, inv_ne_zero hc.ne_zero, fun g => ?_, ?_⟩
  · show c (centralUnif F m * g)⁻¹ = α⁻¹ * c g⁻¹
    have e := centralUnif_zpow_mul_comm (-1) g⁻¹
    have h2 := hc.zpow_mul (-1) g⁻¹
    rw [zpow_neg_one] at e h2
    rw [zpow_neg_one] at h2
    rw [mul_inv_rev, ← e, h2]
  · obtain ⟨C, hC, hCs⟩ := hc.support
    refine ⟨(fun g => g⁻¹) '' C, hC.image continuous_inv, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ := hCs _ hg
    refine ⟨-j, ⟨_, hj, ?_⟩⟩
    show (centralUnif F m ^ j * g⁻¹)⁻¹ = _
    rw [mul_inv_rev, inv_inv, ← zpow_neg, ← centralUnif_zpow_mul_comm]

theorem exists_compact_tile [NeZero m] (hc : IsCentralCoeff m α c) :
    ∃ K : Set (GL (Fin m) F), IsCompact K ∧ ∀ g ∈ tile F m 0, c g ≠ 0 → g ∈ K := by
  classical
  obtain ⟨C, hC, hCs⟩ := hc.support
  have hm : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hcont : Continuous (ordDet : GL (Fin m) F → ℤ) := isLocallyConstant_ordDet_GL.continuous
  obtain ⟨d₁, hd₁⟩ := (hC.image hcont).bddAbove
  obtain ⟨d₀, hd₀⟩ := (hC.image hcont).bddBelow
  refine ⟨⋃ j ∈ Finset.Icc (-|d₀| - 1) |d₁|, (fun h => centralUnif F m ^ (-j) * h) '' C,
    (Finset.Icc (-|d₀| - 1) |d₁|).isCompact_biUnion fun j _ => hC.image (continuous_mul_left _),
    fun g hg hcg => ?_⟩
  obtain ⟨j, hj⟩ := hCs g hcg
  have h1 := hd₁ ⟨_, hj, rfl⟩
  have h0 := hd₀ ⟨_, hj, rfl⟩
  simp only [ordDet_centralUnif_zpow_mul] at h1 h0
  obtain ⟨hg0, hg1⟩ := hg
  simp only [zero_mul, zero_add] at hg0 hg1
  refine Set.mem_biUnion (x := j) ?_ ⟨_, hj, by
    show centralUnif F m ^ (-j) * (centralUnif F m ^ j * g) = g
    rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]⟩
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · by_contra hlt
    push Not at hlt
    have hj1 : j + 1 < 0 := by linarith [abs_nonneg d₀]
    have h2 : (j + 1) * (m : ℤ) ≤ j + 1 := by nlinarith
    have h3 : (j + 1) * (m : ℤ) = j * m + m := by ring
    linarith [neg_abs_le d₀]
  · by_contra hlt
    push Not at hlt
    have : j ≤ j * (m : ℤ) := by nlinarith [abs_nonneg d₁]
    nlinarith [le_abs_self d₁]

theorem exists_bound_tile [NeZero m] (hc : IsCentralCoeff m α c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ tile F m 0, ‖c g‖ ≤ B := by
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun g hg => ?_⟩
  by_cases h : c g = 0
  · rw [h, norm_zero]; exact le_max_right _ _
  · exact (hB g (hKc g hg h)).trans (le_max_left _ _)

end IsCentralCoeff

theorem coe_centralUnif_zpow (j : ℤ) :
    ((centralUnif F m ^ j : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ j) • (1 : Matrix (Fin m) (Fin m) F) := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, Units.val_mul, ih, coe_centralUnif, smul_mul_smul_comm, one_mul,
      ← zpow_add_one₀ hϖ]
  | pred k ih =>
    have hinv : (((centralUnif F m)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((uniformizer F : F)⁻¹) • (1 : Matrix (Fin m) (Fin m) F) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [coe_centralUnif, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hϖ, one_smul]
    rw [_root_.zpow_sub_one, Units.val_mul, ih, hinv, smul_mul_smul_comm, one_mul,
      ← zpow_sub_one₀ hϖ]

theorem IsSchwartzBruhat.exists_ordDet_ge {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ A : ℕ, ∀ g : GL (Fin m) F, Φ (g : Matrix (Fin m) (Fin m) F) ≠ 0 →
      -((m : ℤ) * A) ≤ ordDet g := by
  obtain ⟨r, A, -, hsupp⟩ := hΦ.exists_invariant
  refine ⟨A, fun g hg => ?_⟩
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hent := hsupp _ hg
  have hmem : (((uniformizer F : F) ^ A) • (g : Matrix (Fin m) (Fin m) F)).det ∈ 𝒪[F] :=
    det_mem_integer fun i j => by simpa using hent i j
  have hne : (((uniformizer F : F) ^ A) • (g : Matrix (Fin m) (Fin m) F)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hϖ)) (det_ne_zero g)
  have h := ord_nonneg_of_mem_integer hmem hne
  rw [Matrix.det_smul, LocalField.ord_mul (pow_ne_zero _ (pow_ne_zero _ hϖ)) (det_ne_zero g),
    ← pow_mul, LocalField.ord_pow hϖ, LocalField.ord_uniformizer (irreducible_uniformizer F)] at h
  simp only [Fintype.card_fin] at h
  unfold ordDet
  push_cast at h
  nlinarith

theorem IsSchwartzBruhat.exists_bound {Φ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X, ‖Φ X‖ ≤ B := by
  obtain ⟨B, hB⟩ := hΦ.1.continuous.bounded_above_of_compact_support hΦ.2
  exact ⟨max B 0, le_max_right _ _, fun X => (hB X).trans (le_max_left _ _)⟩

section Integrals

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] [NeZero m] {α : ℂ}
  {c : GL (Fin m) F → ℂ}

theorem norm_detPow_le_of_mem_tile {g : GL (Fin m) F} (hg : g ∈ tile F m 0) (s : ℂ) :
    ‖detPow g s‖ ≤ 1 + ‖qs F s‖ ^ m := by
  obtain ⟨h0, h1⟩ := hg
  simp only [zero_mul, zero_add] at h0 h1
  rw [detPow_eq_qs_zpow, norm_zpow, ← Int.toNat_of_nonneg h0, zpow_natCast]
  have hk : (ordDet g).toNat ≤ m := by omega
  by_cases ht : ‖qs F s‖ ≤ 1
  · have := pow_le_one₀ (norm_nonneg (qs F s)) ht (n := (ordDet g).toNat)
    have := pow_nonneg (norm_nonneg (qs F s)) m
    linarith
  · push Not at ht
    have := pow_le_pow_right₀ ht.le hk
    linarith

theorem IsCentralCoeff.lintegral_tile_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] (s : ℂ) :
    ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ < ∞ := by
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB0, hB⟩ := hc.exists_bound_tile
  set b : ℝ≥0∞ := ENNReal.ofReal (B * (1 + ‖qs F s‖ ^ m))
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  calc ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
      ≤ ∫⁻ g in tile F m 0, K.indicator (fun _ => b) g ∂μ := by
        refine setLIntegral_mono (measurable_const.indicator hKm) fun g hg => ?_
        by_cases hcg : c g = 0
        · simp [hcg]
        · rw [Set.indicator_of_mem (hKc g hg hcg), ← ofReal_norm, norm_mul]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul (hB g hg) (norm_detPow_le_of_mem_tile hg s)
            (norm_nonneg _) hB0)
    _ ≤ ∫⁻ g, K.indicator (fun _ => b) g ∂μ := setLIntegral_le_lintegral _ _
    _ = b * μ K := lintegral_indicator_const hKm b
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem IsCentralCoeff.lintegral_zeta_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1) :
    ∫⁻ g, ‖Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g‖ₑ ∂μ < ∞ := by
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  set ρ : ℝ := ‖α * qs F s ^ m‖ with hρdef
  have hρ0 : 0 < ρ := norm_pos_iff.2 (mul_ne_zero hc.ne_zero (pow_ne_zero _ (qs_ne_zero s)))
  set K₁ := ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
  have hK₁ : K₁ ≠ ∞ := (hc.lintegral_tile_lt_top μ s).ne
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

  have hval : ∀ (j : ℤ) (g : GL (Fin m) F),
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) =
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        (α * qs F s ^ m) ^ j * (c g * detPow g s) := by
    intro j g
    rw [detPow_centralUnif_zpow_mul, IsCentralCoeff.zpow_mul hc, mul_zpow, mul_comm j,
      _root_.zpow_mul, zpow_natCast]
    ring
  rw [lintegral_eq_tsum_tile μ]
  refine tsum_int_lt_top_of_le_geom (j₀ := -(A : ℤ)) (r := ENNReal.ofReal ρ)
    (M := ENNReal.ofReal (BΦ * ρ ^ (-(A : ℤ))) * K₁) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK₁)
    (ENNReal.ofReal_lt_one.2 hs) (fun j hj => ?_) (fun k => ?_)
  · refine (setLIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_).trans (lintegral_zero)
    show ‖_‖ₑ = 0
    rw [enorm_eq_zero]
    by_contra hne
    have hΦne : Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ≠ 0 := by
      intro h; apply hne; rw [h]; ring
    have h1 := hA _ hΦne
    rw [ordDet_centralUnif_zpow_mul] at h1
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    have : (j + 1) * (m : ℤ) ≤ -(A : ℤ) * m := by nlinarith
    nlinarith
  · calc ∫⁻ g in tile F m 0, ‖Φ ((centralUnif F m ^ (-(A : ℤ) + k) * g : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F) * detPow (centralUnif F m ^ (-(A : ℤ) + k) * g) s *
            c (centralUnif F m ^ (-(A : ℤ) + k) * g)‖ₑ ∂μ
        ≤ ∫⁻ g in tile F m 0, (ENNReal.ofReal (BΦ * ρ ^ (-(A : ℤ))) * ENNReal.ofReal ρ ^ k) *
            ‖c g * detPow g s‖ₑ ∂μ := by
          refine lintegral_mono fun g => ?_
          rw [hval, enorm_mul, enorm_mul, ← ofReal_norm, ← ofReal_norm,
            norm_zpow, ← hρdef, zpow_add₀ hρ0.ne', zpow_natCast]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_pow hρ0.le,
            ← ENNReal.ofReal_mul (mul_nonneg hBΦ0 (zpow_nonneg hρ0.le _))]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hBΦ ((centralUnif F m ^ (-(A : ℤ) + k) * g : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F)
          have h2 : 0 ≤ ρ ^ (-(A : ℤ)) * ρ ^ k := mul_nonneg (zpow_nonneg hρ0.le _) (pow_nonneg hρ0.le _)
          nlinarith
      _ = _ := by rw [lintegral_const_mul' _ _ (by
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
                  ring

theorem IsCentralCoeff.integrable_zeta (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1) :
    Integrable (fun g : GL (Fin m) F => Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g) μ :=
  ⟨(((hΦ.1.continuous.comp Units.continuous_val).mul (continuous_detPow s)).mul
      hc.continuous).aestronglyMeasurable, hc.lintegral_zeta_lt_top μ hΦ hs⟩

theorem IsSchwartzBruhat.exists_eq_zero_of_small {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (B : ℕ) :
    ∃ J : ℤ, ∀ j ≥ J, ∀ g : GL (Fin m) F,
      (∀ i l, (g : Matrix (Fin m) (Fin m) F) i l ∈ LocalField.valBall F (-(B : ℤ))) →
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Φ 0 := by
  obtain ⟨r, A, hinv, -⟩ := hΦ.exists_invariant
  refine ⟨(r : ℤ) + B, fun j hj g hg => ?_⟩
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hϖO : (GLnLocal.uniformizer F : F) ∈ 𝒪[F] := (GLnLocal.uniformizer F).2
  set t : ℕ := (j - r - B).toNat with ht
  have hjt : j = (r : ℤ) + B + t := by omega
  have h := hinv 0 ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    (fun i l => ?_)
  · rwa [zero_add] at h
  · refine ⟨(GLnLocal.uniformizer F : F) ^ t * ((GLnLocal.uniformizer F : F) ^ B * (g : Matrix (Fin m) (Fin m) F) i l),
      mul_mem (pow_mem hϖO t) (mem_valBall_neg_iff.1 (hg i l)), ?_⟩
    rw [Units.val_mul, coe_centralUnif_zpow, Matrix.smul_mul, one_mul, Matrix.smul_apply,
      smul_eq_mul, hjt, zpow_add₀ hϖ, zpow_add₀ hϖ, zpow_natCast, zpow_natCast, zpow_natCast]
    ring

theorem IsCentralCoeff.exists_eq_div_zeta (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ (Pn : ℂ[X]) (N : ℕ), ∀ s : ℂ, ‖α * qs F s ^ m‖ < 1 →
      ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g ∂μ =
        Pn.eval (qs F s) / (qs F s ^ N * (1 - α * qs F s ^ m)) := by
  classical
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set J₁ : ℤ := max J (-(A : ℤ))

  set a : ℤ → ℕ → ℂ := fun j k => ∫ g in tile F m 0,
    (if ordDet g = k then Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      c g else 0) ∂μ with hadef
  set P : ℤ → ℂ[X] := fun j => ∑ k ∈ Finset.range m, C (a j k) * X ^ k with hPdef

  have hzero : ∀ j < -(A : ℤ), ∀ g ∈ tile F m 0,
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 0 := by
    intro j hj g hg
    by_contra hne
    have h1 := hA _ hne
    rw [ordDet_centralUnif_zpow_mul] at h1
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    have : (j + 1) * (m : ℤ) ≤ -(A : ℤ) * m := by nlinarith
    nlinarith
  have h0 : ∀ j < -(A : ℤ), P j = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun k _ => ?_
    have : a j k = 0 := by
      refine (setIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_).trans (integral_zero _ _)
      show (if ordDet g = (k : ℤ) then _ else 0) = 0
      rw [hzero j hj g hg]
      simp
    rw [this, map_zero, zero_mul]

  have h1 : ∀ j ≥ J₁, P j = P J₁ := by
    intro j hj
    have hcoef : ∀ k, a j k = a J₁ k := fun k => by
      refine setIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_
      by_cases hcg : c g = 0
      · simp [hcg]
      have hgK := hKc g hg hcg
      have hent := hB _ ⟨g, hgK, rfl⟩
      rw [hJ j (le_trans (le_max_left _ _) hj) g hent,
        hJ J₁ (le_max_left _ _) g hent]
    simp only [hPdef, hcoef]
  obtain ⟨Pn, N, hsum⟩ := hasSum_geom_poly hc.ne_zero m (le_max_right J (-(A : ℤ))) h0 h1
  refine ⟨Pn, N, fun s hs => ?_⟩
  have hint := hc.integrable_zeta μ hΦ hs
  have h := hasSum_integral_tile μ hint
  refine h.unique ?_
  convert hsum (qs F s) (qs_ne_zero s) hs using 1
  funext j
  set x := qs F s with hx

  have hcint : IntegrableOn (fun g => ‖c g‖) (tile F m 0) μ := by
    refine ⟨hc.continuous.norm.aestronglyMeasurable, ?_⟩
    have h0 := hc.lintegral_tile_lt_top μ 0
    have he : ∀ g : GL (Fin m) F, ‖c g * detPow g 0‖ₑ = ‖‖c g‖‖ₑ := fun g => by
      rw [detPow, Complex.cpow_zero, mul_one, enorm_norm]
    simp only [he] at h0
    exact h0
  have hpiece : ∀ k : ℕ, IntegrableOn (fun g => if ordDet g = (k : ℤ) then
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g else 0)
      (tile F m 0) μ := by
    intro k
    refine Integrable.mono' (hcint.const_mul BΦ) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · have hmeas : MeasurableSet {g : GL (Fin m) F | ordDet g = (k : ℤ)} :=
        (isClopen_shell F m k).isOpen.measurableSet
      have hcont : Continuous fun g : GL (Fin m) F =>
          Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g :=
        (hΦ.1.continuous.comp (Units.continuous_val.comp (continuous_const_mul _))).mul
          hc.continuous
      exact (hcont.aestronglyMeasurable.indicator hmeas).congr
        (Filter.Eventually.of_forall fun g => by simp [Set.indicator_apply])
    · split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hBΦ _) (norm_nonneg _)
      · rw [norm_zero]; exact mul_nonneg hBΦ0 (norm_nonneg _)
  have hpt : ∀ g ∈ tile F m 0,
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) =
      (α * x ^ m) ^ j * ∑ k ∈ Finset.range m, x ^ k * (if ordDet g = (k : ℤ) then
        Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g else 0) := by
    intro g hg
    obtain ⟨hg0, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg0 hg1
    have hk : (ordDet g).toNat ∈ Finset.range m := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single_of_mem _ hk (fun k _ hk' => by
      rw [if_neg (by omega), mul_zero])]
    rw [if_pos (Int.toNat_of_nonneg hg0).symm, detPow_centralUnif_zpow_mul,
      IsCentralCoeff.zpow_mul hc, detPow_eq_qs_zpow, ← hx, mul_zpow, mul_comm j, _root_.zpow_mul,
      zpow_natCast, ← Int.toNat_of_nonneg hg0, zpow_natCast]
    simp only [Int.toNat_natCast]
    ring
  show ∫ g in tile F m 0, Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) ∂μ = _
  rw [setIntegral_congr_fun (measurableSet_tile 0) hpt, integral_const_mul,
    integral_finsetSum _ (fun k _ => (hpiece k).const_mul _)]
  simp only [integral_const_mul, hPdef, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hadef]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem IsCentralCoeff.lintegral_weight_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {J : GL (Fin m) F → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞)
    (hJ : ∀ g, J g ≤ B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet g)))
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    ∫⁻ g, ‖c g * detPow g s‖ₑ * J g ∂μ < ∞ := by
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  have hqm0 : 0 < q ^ m := by positivity
  set ρ : ℝ := ‖α * qs F s ^ m‖ with hρdef
  have hρ0 : 0 < ρ := norm_pos_iff.2 (mul_ne_zero hc.ne_zero (pow_ne_zero _ (qs_ne_zero s)))
  set K₁ := ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
  have hK₁ : K₁ ≠ ∞ := (hc.lintegral_tile_lt_top μ s).ne
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hval : ∀ (j : ℤ) (g : GL (Fin m) F),
      c (centralUnif F m ^ j * g) * detPow (centralUnif F m ^ j * g) s =
        (α * qs F s ^ m) ^ j * (c g * detPow g s) := by
    intro j g
    rw [detPow_centralUnif_zpow_mul, IsCentralCoeff.zpow_mul hc, mul_zpow, mul_comm j,
      _root_.zpow_mul, zpow_natCast]
    ring

  have hw : ∀ (j : ℤ) (g : GL (Fin m) F), g ∈ tile F m 0 →
      min 1 ((q ^ m) ^ ordDet (centralUnif F m ^ j * g)) ≤ min 1 ((q ^ m) ^ ((j + 1) * m)) := by
    intro j g hg
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    refine min_le_min le_rfl (zpow_le_zpow_right₀ hqm ?_)
    rw [ordDet_centralUnif_zpow_mul]
    nlinarith
  rw [lintegral_eq_tsum_tile μ]
  set M : ℝ≥0∞ := B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹)
  refine tsum_int_lt_top_of_le_geom₂ (M := M) (r₁ := ENNReal.ofReal ρ)
    (r₂ := ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hK₁) ENNReal.ofReal_ne_top)
    (ENNReal.ofReal_lt_one.2 hs) (ENNReal.ofReal_lt_one.2 ((div_lt_one hρ0).2 hs'))
    (fun k => ?_) (fun k => ?_)
  · calc ∫⁻ g in tile F m 0, ‖c (centralUnif F m ^ ((k : ℕ) : ℤ) * g) *
            detPow (centralUnif F m ^ ((k : ℕ) : ℤ) * g) s‖ₑ *
            J (centralUnif F m ^ ((k : ℕ) : ℤ) * g) ∂μ
        ≤ ∫⁻ g in tile F m 0, (B * ENNReal.ofReal ρ ^ k) * ‖c g * detPow g s‖ₑ ∂μ := by
          refine setLIntegral_mono' (measurableSet_tile 0) fun g hg => ?_
          rw [hval, enorm_mul, ← ofReal_norm, norm_zpow, ← hρdef, zpow_natCast,
            ENNReal.ofReal_pow hρ0.le]
          have hJg := hJ (centralUnif F m ^ ((k : ℕ) : ℤ) * g)
          have hmin : ENNReal.ofReal (min 1 ((q ^ m) ^ ordDet (centralUnif F m ^ ((k : ℕ) : ℤ) * g)))
              ≤ 1 := ENNReal.ofReal_le_one.2 (min_le_left _ _)
          calc ENNReal.ofReal ρ ^ k * ‖c g * detPow g s‖ₑ * J (centralUnif F m ^ ((k : ℕ) : ℤ) * g)
              ≤ ENNReal.ofReal ρ ^ k * ‖c g * detPow g s‖ₑ * (B * 1) := by
                gcongr
                exact hJg.trans (by gcongr)
            _ = _ := by ring
      _ = (B * ENNReal.ofReal ρ ^ k) * K₁ := lintegral_const_mul' _ _
            (ENNReal.mul_ne_top hB (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      _ ≤ M * ENNReal.ofReal ρ ^ k := by
          have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 ρ⁻¹) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
          calc B * ENNReal.ofReal ρ ^ k * K₁ = B * K₁ * 1 * ENNReal.ofReal ρ ^ k := by ring
            _ ≤ B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹) * ENNReal.ofReal ρ ^ k := by gcongr
  · set j : ℤ := -((k : ℤ) + 1) with hj
    have hr : (q ^ m) ^ ((j + 1) * m) = ((q ^ m) ^ (-(m : ℤ))) ^ k := by
      rw [hj, show (-((k : ℤ) + 1) + 1) * (m : ℤ) = -(m : ℤ) * k by ring, _root_.zpow_mul,
        zpow_natCast]
    have hρj : ρ ^ j = ρ⁻¹ * (ρ⁻¹) ^ k := by
      rw [hj, zpow_neg, zpow_add₀ hρ0.ne', zpow_one, zpow_natCast, mul_inv, mul_comm, inv_pow]
    calc ∫⁻ g in tile F m 0, ‖c (centralUnif F m ^ (-((k : ℤ) + 1)) * g) *
            detPow (centralUnif F m ^ (-((k : ℤ) + 1)) * g) s‖ₑ *
            J (centralUnif F m ^ (-((k : ℤ) + 1)) * g) ∂μ
        ≤ ∫⁻ g in tile F m 0, (B * ENNReal.ofReal (ρ⁻¹ * ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k)) *
            ‖c g * detPow g s‖ₑ ∂μ := by
          refine setLIntegral_mono' (measurableSet_tile 0) fun g hg => ?_
          rw [hval, enorm_mul, ← ofReal_norm, norm_zpow, ← hρdef, ← hj]
          have hJg := hJ (centralUnif F m ^ j * g)
          have hmin := ENNReal.ofReal_le_ofReal ((hw j g hg).trans (min_le_right _ _))
          rw [hr] at hmin
          calc ENNReal.ofReal (ρ ^ j) * ‖c g * detPow g s‖ₑ * J (centralUnif F m ^ j * g)
              ≤ ENNReal.ofReal (ρ ^ j) * ‖c g * detPow g s‖ₑ *
                  (B * ENNReal.ofReal (((q ^ m) ^ (-(m : ℤ))) ^ k)) := by
                gcongr
                exact hJg.trans (by gcongr)
            _ = _ := by
                have h1 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
                have h2 : 0 ≤ ρ⁻¹ ^ k := pow_nonneg h1 k
                have h3 : 0 ≤ ((q ^ m) ^ (-(m : ℤ))) ^ k := pow_nonneg (zpow_nonneg hqm0.le _) k
                rw [hρj, div_eq_mul_inv, mul_pow, ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h1,
                  ENNReal.ofReal_mul h3]
                ring
      _ = (B * ENNReal.ofReal (ρ⁻¹ * ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k)) * K₁ :=
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top)
      _ ≤ M * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hρ0.le), ENNReal.ofReal_pow (div_nonneg
            (zpow_nonneg (by positivity) _) hρ0.le)]
          have : ENNReal.ofReal ρ⁻¹ ≤ ENNReal.ofReal (max 1 ρ⁻¹) :=
            ENNReal.ofReal_le_ofReal (le_max_right _ _)
          calc B * (ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k) * K₁
              = B * K₁ * ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by ring
            _ ≤ B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹) * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by
                gcongr

end Integrals

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Measure GJMatrix ValuativeRel
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {m : ℕ} [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

theorem IsSchwartzBruhat.integrable_matrix {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    Integrable Φ (matrixMeasure (n := Fin m) μ₁) :=
  hΦ.1.continuous.integrable_of_hasCompactSupport hΦ.2

theorem integrable_fourier_kernel {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (a b : Matrix (Fin m) (Fin m) F → Matrix (Fin m) (Fin m) F)
    (ha : Continuous a) (hb : Continuous b) (hbi : Integrable (fun X => Ψ (b X)) (matrixMeasure μ₁)) :
    Integrable (fun p : Matrix (Fin m) (Fin m) F × Matrix (Fin m) (Fin m) F =>
      Φ p.1 * ((ψ (Matrix.trace (a p.1 * p.2)) : Circle) : ℂ) * Ψ (b p.2))
      ((matrixMeasure (n := Fin m) μ₁).prod (matrixMeasure μ₁)) := by
  have hprod := (hΦ.integrable_matrix μ₁).mul_prod hbi
  refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((hΦ.1.continuous.comp continuous_fst).mul ((continuous_subtype_val.comp hψ).comp
      (Continuous.matrix_trace ((ha.comp continuous_fst).matrix_mul continuous_snd)))).mul
      ((hΨ.1.continuous.comp hb).comp continuous_snd)).aestronglyMeasurable
  · simp only [norm_mul, Circle.norm_coe, mul_one]
    rfl

theorem integral_fourier_mul {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {f g : Matrix (Fin m) (Fin m) F → ℂ} (hf : IsSchwartzBruhat f) (hg : IsSchwartzBruhat g) :
    ∫ W, localMatrixFourier ψ f W * g W ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ Z, f Z * localMatrixFourier ψ g Z ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  have hint := integrable_fourier_kernel hψ hf hg (LocalField.selfDualMeasure ψ) id id continuous_id
    continuous_id (hg.integrable_matrix _)
  simp only [id] at hint
  have h1 : ∫ W, localMatrixFourier ψ f W * g W ∂M = ∫ W, ∫ Z, f Z *
      ((ψ (Matrix.trace (Z * W)) : Circle) : ℂ) * g W ∂M ∂M := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [localMatrixFourier]
    rw [← integral_mul_const]
  have h2 : ∫ Z, f Z * localMatrixFourier ψ g Z ∂M = ∫ Z, ∫ W, f Z *
      ((ψ (Matrix.trace (Z * W)) : Circle) : ℂ) * g W ∂M ∂M := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
    simp only [localMatrixFourier]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only
    rw [Matrix.trace_mul_comm W Z]
    ring
  rw [h1, h2, ← integral_prod_symm _ hint, integral_prod _ hint]

theorem localMatrixFourier_comp_mul_left {ψ : AddChar F Circle} (Φ : Matrix (Fin m) (Fin m) F → ℂ)
    (y : GL (Fin m) F) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (fun Z => Φ ((y : Matrix (Fin m) (Fin m) F) * Z)) W =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        localMatrixFourier ψ Φ (W * ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
  have h := integral_comp_mul_left_matrix (LocalField.selfDualMeasure ψ) y
    (fun Z => Φ Z * ((ψ (Matrix.trace (Z * (W * ((y⁻¹ : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F)))) : Circle) : ℂ))
  have htr : ∀ Z : Matrix (Fin m) (Fin m) F, Matrix.trace ((y : Matrix (Fin m) (Fin m) F) * Z *
      (W * ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))) = Matrix.trace (Z * W) := by
    intro Z
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  simp only [localMatrixFourier]
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only [htr]

theorem integral_fourier_mul_right {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (y : GL (Fin m) F) :
    ∫ X, localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ X, Φ ((y : Matrix (Fin m) (Fin m) F) * X) * localMatrixFourier ψ Ψ X
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
  set d : ℝ := (LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m with hd
  have hd0 : d ≠ 0 := pow_ne_zero _ (by
    exact_mod_cast (LocalField.modulus_ne_zero (det_ne_zero y)))

  have h1 := integral_comp_mul_right_matrix (LocalField.selfDualMeasure ψ) y⁻¹
    (fun X => localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F)))
  have hdinv : (LocalField.modulus ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m =
      d⁻¹ := by
    rw [hd, ← inv_pow]
    congr 1
    have hm := LocalField.modulus_mul ((y : Matrix (Fin m) (Fin m) F).det)
      ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      LocalField.modulus_one] at hm
    have h' : (LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) *
        (LocalField.modulus ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det : ℝ) = 1 := by
      exact_mod_cast hm.symm
    exact eq_inv_of_mul_eq_one_right h'
  rw [hdinv, inv_inv] at h1
  have h2 : ∫ X, localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))
      ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ W, localMatrixFourier ψ (fun Z => Φ ((y : Matrix (Fin m) (Fin m) F) * Z)) W * Ψ W
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
    rw [← inv_smul_smul₀ hd0 (∫ X, _ ∂_), ← h1, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only
    rw [localMatrixFourier_comp_mul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one, smul_mul_assoc]
  rw [h2, integral_fourier_mul hψ (hΦ.comp_mul_left y) hΨ]

theorem lintegral_comp_linearEquiv {ι : Type*} [Fintype ι] (μ₀ : Measure (ι → F))
    [μ₀.IsAddHaarMeasure] (L : (ι → F) ≃ₗ[F] (ι → F)) (f : (ι → F) → ℝ≥0∞) :
    ∫⁻ x, f (L x) ∂μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) * ∫⁻ x, f x ∂μ₀ := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLic : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  let e : (ι → F) ≃ₜ (ι → F) := ⟨L.toEquiv, hLc, hLic⟩
  have hmap : Measure.map L μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) • μ₀ := by
    ext S hS
    rw [Measure.map_apply hLc.measurable hS, Measure.smul_apply]
    have h := distribHaarChar_mul μ₀ L⁻¹ S
    have hpre : (L : (ι → F) → (ι → F)) ⁻¹' S = L⁻¹ • S := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, LinearEquiv.smul_def]
      rfl
    rw [hpre, ← h, map_inv, ENNReal.smul_def, smul_eq_mul]
  have := e.measurableEmbedding.lintegral_map (μ := μ₀) f
  change ∫⁻ y, f y ∂(Measure.map L μ₀) = _ at this
  calc ∫⁻ x, f (L x) ∂μ₀ = ∫⁻ x, f (e x) ∂μ₀ := rfl
    _ = _ := by rw [← this, hmap, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_mul_right_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℝ≥0∞) :
    ∫⁻ X, f (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) *
        ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hemb := (Measures.entriesHomeomorph F m).measurableEmbedding
  have hconv : ∀ g : Matrix (Fin m) (Fin m) F → ℝ≥0∞, ∫⁻ X, g X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫⁻ x, g ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := fun g => by
    rw [← hmp.lintegral_comp_emb hemb]
    rfl
  rw [hconv, hconv]
  have h := lintegral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).right y) (fun x => f ((Measures.entries F m).symm x))
  have hR : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).right y x) =
      (Measures.entries F m).symm x * (y : Matrix (Fin m) (Fin m) F) := fun x => by
    simp [Measures.glChart]
  simp only [hR] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_rightModulus F m y
  rw [Measures.LinearChart.rightModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]

theorem lintegral_comp_mul_left_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℝ≥0∞) :
    ∫⁻ X, f ((y : Matrix (Fin m) (Fin m) F) * X) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) *
        ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hemb := (Measures.entriesHomeomorph F m).measurableEmbedding
  have hconv : ∀ g : Matrix (Fin m) (Fin m) F → ℝ≥0∞, ∫⁻ X, g X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫⁻ x, g ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := fun g => by
    rw [← hmp.lintegral_comp_emb hemb]
    rfl
  rw [hconv, hconv]
  have h := lintegral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).left y) (fun x => f ((Measures.entries F m).symm x))
  have hL : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).left y x) =
      (y : Matrix (Fin m) (Fin m) F) * (Measures.entries F m).symm x := fun x => by
    simp [Measures.glChart]
  simp only [hL] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_leftModulus F m y
  rw [Measures.LinearChart.leftModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]

theorem inv_modulus_det_pow (y : GL (Fin m) F) :
    (((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) : ℝ) =
      ((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y := by
  rw [LocalField.modulus_of_ne_zero (det_ne_zero y)]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ordDet]
  congr 1
  ring

theorem IsSchwartzBruhat.lintegral_lt_top {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∫⁻ X, ‖Φ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ < ∞ :=
  (hΦ.integrable_matrix μ₁).2

theorem exists_bound_kernel₁ {Φ' Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ' : IsSchwartzBruhat Φ')
    (hΨ : IsSchwartzBruhat Ψ) (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ y : GL (Fin m) F,
      ∫⁻ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
        B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y)) := by
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ'.exists_bound
  obtain ⟨A, hA⟩ := hΦ'.exists_ordDet_ge
  obtain ⟨K, hK, hKΨ⟩ := hΨK
  obtain ⟨e₁, he₁⟩ := (hK.image isLocallyConstant_ordDet_GL.continuous).bddAbove
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  set k₂ : ℤ := e₁ + m * A
  set C₁ : ℝ≥0∞ := ENNReal.ofReal BΦ * ∫⁻ X, ‖Ψ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ with hC₁def
  have hC₁ : C₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΨ.lintegral_lt_top μ₁).ne
  clear_value C₁
  refine ⟨C₁ * ENNReal.ofReal ((q ^ m) ^ max k₂ 0), ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top,
    fun y => ?_⟩
  by_cases hy : k₂ < ordDet y
  ·
    have hz : ∀ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ = 0 := by
      intro X
      rw [enorm_eq_zero]
      by_contra hne
      have hΨne : Ψ (X * (y : Matrix (Fin m) (Fin m) F)) ≠ 0 := right_ne_zero_of_mul hne
      have hΦne : Φ' X ≠ 0 := left_ne_zero_of_mul hne
      obtain ⟨k, hk, hkX⟩ := hKΨ _ hΨne
      have hX : X = ((k * y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
        rw [Units.val_mul, hkX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      rw [hX] at hΦne
      have h1 := hA _ hΦne
      rw [ordDet_mul, ordDet_inv] at h1
      have h2 := he₁ ⟨k, hk, rfl⟩
      omega
    simp [hz]
  · push Not at hy
    calc ∫⁻ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂matrixMeasure (n := Fin m) μ₁
        ≤ ∫⁻ X, ENNReal.ofReal BΦ * ‖Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ
            ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm]
          gcongr
          exact hBΦ X
      _ = C₁ * ENNReal.ofReal ((q ^ m) ^ ordDet y) := by
          rw [hC₁def, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_comp_mul_right_matrix μ₁ y (fun X => ‖Ψ X‖ₑ), ← inv_modulus_det_pow,
            ENNReal.ofReal_coe_nnreal]
          ring
      _ ≤ C₁ * ENNReal.ofReal ((q ^ m) ^ max k₂ 0) * ENNReal.ofReal (min 1 ((q ^ m) ^ ordDet y)) := by
          rw [mul_assoc]
          gcongr C₁ * ?_
          rw [← ENNReal.ofReal_mul (zpow_nonneg (by positivity) _)]
          refine ENNReal.ofReal_le_ofReal ?_
          by_cases h0 : ordDet y ≤ 0
          · rw [min_eq_right (zpow_le_one_of_nonpos₀ hqm h0)]
            exact le_mul_of_one_le_left (zpow_nonneg (by positivity) _) (one_le_zpow₀ hqm
              (le_max_right _ _))
          · push Not at h0
            rw [min_eq_left (one_le_zpow₀ hqm h0.le), mul_one]
            exact zpow_le_zpow_right₀ hqm (le_trans hy (le_max_left _ _))

theorem exists_bound_kernel₂ {Φ Ψ' : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (hΨ' : IsSchwartzBruhat Ψ') (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ y : GL (Fin m) F,
      ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
        B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y)) := by
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  obtain ⟨BΨ, hBΨ0, hBΨ⟩ := hΨ'.exists_bound
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  set C₂ : ℝ≥0∞ := ENNReal.ofReal BΨ * ∫⁻ X, ‖Φ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁
  set C₃ : ℝ≥0∞ := ENNReal.ofReal BΦ * ∫⁻ X, ‖Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁
  have hC₂ : C₂ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΦ.lintegral_lt_top μ₁).ne
  have hC₃ : C₃ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΨ'.lintegral_lt_top μ₁).ne
  refine ⟨max C₂ C₃, max_ne_top hC₂ hC₃, fun y => ?_⟩
  have h2 : ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
      C₂ * ENNReal.ofReal ((q ^ m) ^ ordDet y) := by
    calc _ ≤ ∫⁻ X, ENNReal.ofReal BΨ * ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X)‖ₑ
            ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm (Ψ' X), mul_comm]
          gcongr
          exact hBΨ X
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_comp_mul_left_matrix μ₁ y (fun X => ‖Φ X‖ₑ), ← inv_modulus_det_pow,
            ENNReal.ofReal_coe_nnreal]
          ring
  have h3 : ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
      C₃ := by
    calc _ ≤ ∫⁻ X, ENNReal.ofReal BΦ * ‖Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm (Φ _)]
          gcongr
          exact hBΦ _
      _ = C₃ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  by_cases h0 : (q ^ m) ^ ordDet y ≤ 1
  · rw [min_eq_right h0]
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · push Not at h0
    rw [min_eq_left h0.le, ENNReal.ofReal_one, mul_one]
    exact h3.trans (le_max_right _ _)

theorem detPow_mul_detPow (g : GL (Fin m) F) (a b : ℂ) : detPow g a * detPow g b = detPow g (a + b) := by
  have h : (absDet g : ℂ) ≠ 0 := by
    rw [absDet]
    exact_mod_cast LocalField.modulus_ne_zero (det_ne_zero g)
  rw [detPow, detPow, detPow, Complex.cpow_add _ _ h]

theorem enorm_detPow_natCast (g : GL (Fin m) F) :
    ‖detPow g (m : ℂ)‖ₑ = ((detModulusPow g : ℝ≥0) : ℝ≥0∞) := by
  rw [detPow_natCast, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]

def shearLeft (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : G × G ≃ₜ G × G where
  toFun z := (z.1, z.1 * z.2)
  invFun z := (z.1, z.1⁻¹ * z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_fst.mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.mul continuous_snd)

def shearRight (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : G × G ≃ₜ G × G where
  toFun z := (z.1 * z.2, z.2)
  invFun z := (z.1 * z.2⁻¹, z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := (continuous_fst.mul continuous_snd).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul continuous_snd.inv).prodMk continuous_snd

variable [NeZero m] {α : ℂ} {c : GL (Fin m) F → ℂ}

theorem integral_kernel_left (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {κ : ℝ≥0} (hκint : ∀ f : Matrix (Fin m) (Fin m) F → ℂ,
      ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
        (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ))
    (hκlint : ∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
      ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
        κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)) :
    ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Φ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (h⁻¹ * g) ∂μ) ∂μ =
      ∫ y, detPow y s * c y * ((κ : ℝ) • ∫ X, localMatrixFourier ψ Φ X *
        Ψ (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m)
          (LocalField.selfDualMeasure ψ)) ∂μ := by
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  set Φh := localMatrixFourier ψ Φ with hΦhdef
  have hΦh : IsSchwartzBruhat Φh := hΦ.localMatrixFourier hψ hψ1
  set F₁ : GL (Fin m) F × GL (Fin m) F → ℂ := fun p =>
    Φh (p.1 : Matrix (Fin m) (Fin m) F) * detPow p.1 (m - s) *
      (Ψ (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 s) * c (p.1⁻¹ * p.2) with hF₁
  have hT : MeasurePreserving (shearLeft (GL (Fin m) F)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_mul μ μ
  have hTe : MeasurableEmbedding (shearLeft (GL (Fin m) F)) := (shearLeft _).measurableEmbedding
  have hF₁T : ∀ p : GL (Fin m) F × GL (Fin m) F, F₁ (shearLeft _ p) =
      (Φh (p.1 : Matrix (Fin m) (Fin m) F) * Ψ ((p.1 : Matrix (Fin m) (Fin m) F) *
        (p.2 : Matrix (Fin m) (Fin m) F)) * detPow p.1 (m : ℂ)) * (detPow p.2 s * c p.2) := by
    intro p
    simp only [hF₁, shearLeft, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, inv_mul_cancel_left,
      Units.val_mul, detPow_mul]
    have hadd := detPow_mul_detPow p.1 ((m : ℂ) - s) s
    rw [sub_add_cancel] at hadd
    rw [← hadd]
    ring

  have hcontT : Continuous (F₁ ∘ shearLeft (GL (Fin m) F)) := by
    have : (F₁ ∘ shearLeft (GL (Fin m) F)) = fun p => (Φh (p.1 : Matrix (Fin m) (Fin m) F) *
        Ψ ((p.1 : Matrix (Fin m) (Fin m) F) * (p.2 : Matrix (Fin m) (Fin m) F)) *
        detPow p.1 (m : ℂ)) * (detPow p.2 s * c p.2) := funext hF₁T
    rw [this]
    exact (((hΦh.1.continuous.comp (Units.continuous_val.comp continuous_fst)).mul
      (hΨ.1.continuous.comp ((Units.continuous_val.comp continuous_fst).mul
        (Units.continuous_val.comp continuous_snd)))).mul
      ((continuous_detPow _).comp continuous_fst)).mul
      (((continuous_detPow _).comp continuous_snd).mul (hc.continuous.comp continuous_snd))
  obtain ⟨B₁, hB₁, hbound⟩ := exists_bound_kernel₁ hΦh hΨ hΨK (LocalField.selfDualMeasure ψ)
  have hlint : ∫⁻ p, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) p‖ₑ ∂(μ.prod μ) < ∞ := by
    rw [lintegral_prod_symm _ hcontT.enorm.measurable.aemeasurable]
    have hin : ∀ y : GL (Fin m) F, ∫⁻ h, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) (h, y)‖ₑ ∂μ =
        ‖c y * detPow y s‖ₑ * (κ * ∫⁻ X, ‖Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂M) := by
      intro y
      have e1 : ∀ h : GL (Fin m) F, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) (h, y)‖ₑ =
          ‖Φh (h : Matrix (Fin m) (Fin m) F) * Ψ ((h : Matrix (Fin m) (Fin m) F) *
            (y : Matrix (Fin m) (Fin m) F))‖ₑ * (detModulusPow h : ℝ≥0∞) *
            ‖c y * detPow y s‖ₑ := fun h => by
        rw [Function.comp_apply, hF₁T, enorm_mul, enorm_mul, enorm_detPow_natCast, mul_comm (detPow y s)]
      simp only [e1]
      rw [lintegral_mul_const' _ _ enorm_ne_top,
        hκlint (fun X => ‖Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ)
        ((hΦh.1.continuous.mul (hΨ.1.continuous.comp (continuous_id.mul continuous_const))).enorm.measurable)]
      ring
    simp only [hin]
    exact hc.lintegral_weight_lt_top μ (J := fun y => κ * ∫⁻ X, ‖Φh X *
      Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂M) (B := κ * B₁)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hB₁) (fun y => by
        rw [mul_assoc]
        gcongr
        exact hbound y) hs hs'
  have hF₁Ti : Integrable (F₁ ∘ shearLeft (GL (Fin m) F)) (μ.prod μ) :=
    ⟨hcontT.aestronglyMeasurable, hlint⟩
  have hF₁i : Integrable F₁ (μ.prod μ) := (hT.integrable_comp_emb hTe).1 hF₁Ti
  calc ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, Φh (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) * c (h⁻¹ * g) ∂μ) ∂μ
      = ∫ g, ∫ h, F₁ (h, g) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hF₁]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        simp only
        ring
    _ = ∫ p, F₁ p ∂(μ.prod μ) := (integral_prod_symm F₁ hF₁i).symm
    _ = ∫ p, F₁ (shearLeft (GL (Fin m) F) p) ∂(μ.prod μ) := (hT.integral_comp hTe F₁).symm
    _ = ∫ y, ∫ h, F₁ (shearLeft (GL (Fin m) F) (h, y)) ∂μ ∂μ := integral_prod_symm _ hF₁Ti
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hF₁T]
        rw [integral_mul_const, hκint (fun X => Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F)))]
        ring

theorem integral_kernel_right (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {κ : ℝ≥0} (hκint : ∀ f : Matrix (Fin m) (Fin m) F → ℂ,
      ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
        (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ))
    (hκlint : ∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
      ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
        κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)) :
    ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Ψ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (g * h⁻¹) ∂μ) ∂μ =
      ∫ y, detPow y s * c y * ((κ : ℝ) • ∫ X, Φ ((y : Matrix (Fin m) (Fin m) F) * X) *
        localMatrixFourier ψ Ψ X ∂matrixMeasure (n := Fin m)
          (LocalField.selfDualMeasure ψ)) ∂μ := by
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F m μ
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  set Ψh := localMatrixFourier ψ Ψ with hΨhdef
  have hΨh : IsSchwartzBruhat Ψh := hΨ.localMatrixFourier hψ hψ1
  set F₂ : GL (Fin m) F × GL (Fin m) F → ℂ := fun p =>
    Φ (p.1 : Matrix (Fin m) (Fin m) F) * detPow p.1 s *
      (Ψh (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 (m - s)) * c (p.1 * p.2⁻¹) with hF₂
  have hT : MeasurePreserving (shearRight (GL (Fin m) F)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_mul_prod μ μ
  have hTe : MeasurableEmbedding (shearRight (GL (Fin m) F)) := (shearRight _).measurableEmbedding
  have hF₂T : ∀ p : GL (Fin m) F × GL (Fin m) F, F₂ (shearRight _ p) =
      (Φ ((p.1 : Matrix (Fin m) (Fin m) F) * (p.2 : Matrix (Fin m) (Fin m) F)) *
        Ψh (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 (m : ℂ)) * (detPow p.1 s * c p.1) := by
    intro p
    simp only [hF₂, shearRight, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mul_inv_cancel_right,
      Units.val_mul, detPow_mul]
    have hadd := detPow_mul_detPow p.2 s ((m : ℂ) - s)
    rw [add_sub_cancel] at hadd
    rw [← hadd]
    ring
  have hcontT : Continuous (F₂ ∘ shearRight (GL (Fin m) F)) := by
    have : (F₂ ∘ shearRight (GL (Fin m) F)) = fun p => (Φ ((p.1 : Matrix (Fin m) (Fin m) F) *
        (p.2 : Matrix (Fin m) (Fin m) F)) * Ψh (p.2 : Matrix (Fin m) (Fin m) F) *
        detPow p.2 (m : ℂ)) * (detPow p.1 s * c p.1) := funext hF₂T
    rw [this]
    exact (((hΦ.1.continuous.comp ((Units.continuous_val.comp continuous_fst).mul
        (Units.continuous_val.comp continuous_snd))).mul
      (hΨh.1.continuous.comp (Units.continuous_val.comp continuous_snd))).mul
      ((continuous_detPow _).comp continuous_snd)).mul
      (((continuous_detPow _).comp continuous_fst).mul (hc.continuous.comp continuous_fst))
  obtain ⟨B₂, hB₂, hbound⟩ := exists_bound_kernel₂ hΦ hΨh (LocalField.selfDualMeasure ψ)
  have hlint : ∫⁻ p, ‖(F₂ ∘ shearRight (GL (Fin m) F)) p‖ₑ ∂(μ.prod μ) < ∞ := by
    rw [lintegral_prod _ hcontT.enorm.measurable.aemeasurable]
    have hin : ∀ y : GL (Fin m) F, ∫⁻ h, ‖(F₂ ∘ shearRight (GL (Fin m) F)) (y, h)‖ₑ ∂μ =
        ‖c y * detPow y s‖ₑ * (κ * ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X‖ₑ ∂M) := by
      intro y
      have e1 : ∀ h : GL (Fin m) F, ‖(F₂ ∘ shearRight (GL (Fin m) F)) (y, h)‖ₑ =
          ‖Φ ((y : Matrix (Fin m) (Fin m) F) * (h : Matrix (Fin m) (Fin m) F)) *
            Ψh (h : Matrix (Fin m) (Fin m) F)‖ₑ * (detModulusPow h : ℝ≥0∞) *
            ‖c y * detPow y s‖ₑ := fun h => by
        rw [Function.comp_apply, hF₂T, enorm_mul, enorm_mul, enorm_detPow_natCast,
          mul_comm (detPow y s)]
      simp only [e1]
      rw [lintegral_mul_const' _ _ enorm_ne_top,
        hκlint (fun X => ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X‖ₑ)
        (((hΦ.1.continuous.comp (continuous_const.mul continuous_id)).mul
          hΨh.1.continuous).enorm.measurable)]
      ring
    simp only [hin]
    exact hc.lintegral_weight_lt_top μ (J := fun y => κ * ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) *
      X) * Ψh X‖ₑ ∂M) (B := κ * B₂)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hB₂) (fun y => by
        rw [mul_assoc]
        gcongr
        exact hbound y) hs hs'
  have hF₂Ti : Integrable (F₂ ∘ shearRight (GL (Fin m) F)) (μ.prod μ) :=
    ⟨hcontT.aestronglyMeasurable, hlint⟩
  have hF₂i : Integrable F₂ (μ.prod μ) := (hT.integrable_comp_emb hTe).1 hF₂Ti
  calc ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, Ψh (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) * c (g * h⁻¹) ∂μ) ∂μ
      = ∫ g, ∫ h, F₂ (g, h) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hF₂]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        simp only
        ring
    _ = ∫ p, F₂ p ∂(μ.prod μ) := (integral_prod F₂ hF₂i).symm
    _ = ∫ p, F₂ (shearRight (GL (Fin m) F) p) ∂(μ.prod μ) := (hT.integral_comp hTe F₂).symm
    _ = ∫ y, ∫ h, F₂ (shearRight (GL (Fin m) F) (y, h)) ∂μ ∂μ := integral_prod _ hF₂Ti
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hF₂T]
        rw [integral_mul_const, hκint (fun X => Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X)]
        ring

theorem integral_kernel_eq (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Φ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (h⁻¹ * g) ∂μ) ∂μ =
      ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Ψ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (g * h⁻¹) ∂μ) ∂μ := by
  obtain ⟨κ, -, hκint, hκlint⟩ := exists_integral_GL_eq μ (LocalField.selfDualMeasure ψ)
  rw [integral_kernel_left hc μ hψ hψ1 hΦ hΨ hΨK hs hs' hκint hκlint,
    integral_kernel_right hc μ hψ hψ1 hΦ hΨ hs hs' hκint hκlint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_fourier_mul_right hψ hΦ hΨ y]

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open SchurOrthogonality

variable {𝔊 : Type*} [Group 𝔊] [TopologicalSpace 𝔊] [IsTopologicalGroup 𝔊] [LocallyCompactSpace 𝔊]
  [T2Space 𝔊] [TotallyDisconnectedSpace 𝔊]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ 𝔊 W}

theorem apply_fixedProj_of_invariant (hρ : IsSmooth ρ) {K : Subgroup 𝔊}
    (hKc : IsCompact (K : Set 𝔊)) (hKo : IsOpen (K : Set 𝔊)) {f : W →ₗ[ℂ] ℂ}
    (hf : ∀ k ∈ K, ∀ w, f (ρ k w) = f w) (w : W) :
    f (fixedProj ρ hρ hKc hKo w) = f w := by
  have hs := sub_fixedProj_mem hρ hKc hKo w
  have := coinvariantsKer_le_ker_of_invariant hf hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  exact this.symm

theorem exists_smul_of_bilinear (hρ : IsAdmissible ρ) [ρ.IsIrreducible] {K : Subgroup 𝔊}
    (hKc : IsCompact (K : Set 𝔊)) (hKo : IsOpen (K : Set 𝔊))
    (b : W →ₗ[ℂ] smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ)
    (hinvR : ∀ u ∈ fixedVectors ρ K, ∀ k ∈ K, ∀ l, b u (contragredient ρ k l) = b u l)
    (hinvL : ∀ l ∈ fixedVectors (contragredient ρ) K, ∀ k ∈ K, ∀ w, b (ρ k w) l = b w l)
    (hcomm : ∀ u ∈ fixedVectors ρ K, ∀ l ∈ fixedVectors (contragredient ρ) K, ∀ z,
      b (ρ z u) l = b u (contragredient ρ z⁻¹ l)) :
    ∃ c : ℂ, ∀ u ∈ fixedVectors ρ K, ∀ l : smoothVectors (Representation.dual ρ),
      b u l = c * (l : Module.Dual ℂ W) u := by
  classical
  set U := fixedVectors ρ K
  have : FiniteDimensional ℂ U := hρ.2 K hKc hKo
  set FC := fixedVectors (contragredient ρ) K
  set e := fixedContragredientEquiv hρ.1 hKc hKo with he
  set β : U →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ U) :=
    (b ∘ₗ U.subtype).compl₂ (FC.subtype ∘ₗ (e.symm : Module.Dual ℂ U →ₗ[ℂ] FC)) with hβ
  set T : U →ₗ[ℂ] U := (Module.evalEquiv ℂ U).symm.toLinearMap ∘ₗ β with hTdef
  have hT : ∀ (u : U) (φ : Module.Dual ℂ U), φ (T u) = b u (e.symm φ : FC) := by
    intro u φ
    have h := congrArg (fun ψ : Module.Dual ℂ (Module.Dual ℂ U) => ψ φ)
      ((Module.evalEquiv ℂ U).apply_symm_apply (β u))
    simpa [hTdef, Module.evalEquiv_apply, hβ] using h
  have hTl : ∀ (u : U) (l : FC), ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) (T u) = b u l := by
    intro u l
    have h := hT u (e l)
    rw [e.symm_apply_apply] at h
    have h2 : (e l) (T u) = ((l : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ W)
        (T u) := by
      rw [he, fixedContragredientEquiv_apply, restrictFixed_apply]
    rw [← h2, h]

  have hText : ∀ (u : U) (l : smoothVectors (Representation.dual ρ)),
      b u l = (l : Module.Dual ℂ W) (T u) := by
    intro u
    let g : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ :=
      { toFun := fun l => (l : Module.Dual ℂ W) (T u)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have heq := eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (f := b u) (g := g)
      (fun k hk l => hinvR u u.2 k hk l)
      (fun k hk l => by
        show ((contragredient ρ k l : smoothVectors (Representation.dual ρ)) :
          Module.Dual ℂ W) (T u) = (l : Module.Dual ℂ W) (T u)
        rw [contragredient_apply_apply, (T u).2 k⁻¹ (inv_mem hk)])
      (fun l hl => (hTl u ⟨l, hl⟩).symm)
    exact fun l => LinearMap.congr_fun heq l

  have hsep : ∀ x : U, (∀ l : FC, ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) x = 0) → x = 0 := by
    intro x hx
    refine (Module.forall_dual_apply_eq_zero_iff ℂ x).1 fun φ => ?_
    have := hx (e.symm φ)
    rw [← this]
    conv_lhs => rw [← e.apply_symm_apply φ]
    rw [he, fixedContragredientEquiv_apply, restrictFixed_apply]

  set E := fixedProj ρ hρ.1 hKc hKo
  set S : 𝔊 → U →ₗ[ℂ] U := fun z => E ∘ₗ ρ z ∘ₗ U.subtype with hS
  have hEl : ∀ l : FC, ∀ w : W, ((l : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ W) (E w) = (l : Module.Dual ℂ W) w := fun l w =>
    apply_fixedProj_of_invariant hρ.1 hKc hKo (f := (l : Module.Dual ℂ W))
      (fun k hk v => (mem_fixedVectors_contragredient.1 l.2) k hk v) w
  have hcommT : ∀ z (u : U), T (S z u) = S z (T u) := by
    intro z u
    rw [← sub_eq_zero]
    refine hsep _ fun l => ?_
    rw [Submodule.coe_sub, map_sub, sub_eq_zero]
    rw [hTl, show S z (T u) = E (ρ z (T u)) from rfl, hEl]
    have h1 : b (S z u) l = b (ρ z u) l := by
      show b (E (ρ z u)) l = b (ρ z u) l
      exact apply_fixedProj_of_invariant hρ.1 hKc hKo (f := b.flip l)
        (fun k hk w => hinvL l l.2 k hk w) _
    rw [h1, hcomm u u.2 l l.2 z, hText u]
    rw [contragredient_apply_apply, inv_inv]

  have hspan : ∀ x : U, x ≠ 0 → ∀ y : U, y ∈ Submodule.span ℂ (Set.range fun z => S z x) := by
    intro x hx y
    have hx' : (x : W) ≠ 0 := fun h => hx (Subtype.ext h)
    have hy : (y : W) ∈ Submodule.span ℂ (Set.range fun z => ρ z (x : W)) := by
      rw [span_orbit_eq_top hx']; trivial
    have hmap := Submodule.mem_map_of_mem (f := E) hy
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    rwa [show E (y : W) = y from Subtype.ext (fixedProj_apply_of_mem hρ.1 hKc hKo y.2)] at hmap

  by_cases htriv : Subsingleton U
  · refine ⟨0, fun u hu l => ?_⟩
    have : (⟨u, hu⟩ : U) = 0 := Subsingleton.elim _ _
    have hu0 : u = 0 := congrArg Subtype.val this
    rw [hu0, map_zero, LinearMap.zero_apply, map_zero, mul_zero]
  · rw [not_subsingleton_iff_nontrivial] at htriv
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hall : ∀ y : U, T y = c • y := by
      intro y
      have hmem : y ∈ Module.End.eigenspace T c := by
        refine Submodule.span_le.2 ?_ (hspan x hx.2 y)
        rintro _ ⟨z, rfl⟩
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
        show T (S z x) = c • S z x
        rw [hcommT,
          (Module.End.mem_eigenspace_iff.1 hx.1), map_smul]
      exact Module.End.mem_eigenspace_iff.1 hmem
    refine ⟨c, fun u hu l => ?_⟩
    rw [show u = ((⟨u, hu⟩ : U) : W) from rfl, hText, hall, Submodule.coe_smul, map_smul,
      smul_eq_mul]

end GodementJacquet

end GroundTheory.Automorphic
end
end
