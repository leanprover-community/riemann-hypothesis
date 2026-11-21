import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycSeries

section Abstract

variable {C : Type} [NormedField C]

theorem mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by
  simp only [Matrix.mulVec, dotProduct]
  exact X.sum_mem fun b _ => hB a b _ (hv b)

theorem inj_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C)
    (hgX : ∀ x ∈ X, g x ∈ X) (p q : C) (hp : p ≠ 0) (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (hgq : g q = q)
    (S : C → C) (hS : ∀ x ∈ X, S x ∈ X ∧ S (g x - x) = p * x)
    (hlin : ∀ x ∈ X, S (p * q * x) = p * q * S x)
    (B : Matrix (Fin r) (Fin r) C) (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X)
    (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) : y = 0 := by
  have key : ∀ n : ℕ, ∀ y : Fin r → C, (∀ a, y a ∈ X) →
      (∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = 0) → ∀ a, ‖y a‖ ≤ ‖q‖ ^ n := by
    intro n
    induction n with
    | zero => intro y hy _ a; simpa using hX1 _ (hy a)
    | succ n ih =>
      intro y hy h a
      have hm : ∀ a, -B.mulVec (fun b => g (y b)) a ∈ X := fun a =>
        X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hy b)) a)
      let z : Fin r → C := fun a => S (-B.mulVec (fun b => g (y b)) a)
      have hyz : ∀ a, y a = q * z a := fun a => by
        apply mul_left_cancel₀ hp
        rw [← (hS _ (hy a)).2, eq_neg_of_add_eq_zero_left (h a), ← mul_neg, hlin _ (hm a), mul_assoc]
      have := ih z (fun a => (hS _ (hm a)).1) (fun a => by
        apply mul_left_cancel₀ hq
        have h1 := h a
        have e : (fun b => g (y b)) = q • fun b => g (z b) := by
          funext b; rw [hyz b, map_mul, hgq]; rfl
        rw [e, Matrix.mulVec_smul, hyz a, map_mul, hgq, Pi.smul_apply, smul_eq_mul] at h1
        linear_combination h1) a
      rw [hyz a, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  funext a
  exact norm_le_zero_iff.1 (ge_of_tendsto'
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1) fun n => key n y hy h a)

theorem surj_of_small [CompleteSpace C] {r : ℕ} (X : AddSubgroup C) (hX : IsClosed (X : Set C))
    (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (g : C ≃+* C) (hg : Continuous g) (hgX : ∀ x ∈ X, g x ∈ X)
    (p q : C) (hq1 : ‖q‖ < 1) (hgq : g q = q) (hqX : ∀ x ∈ X, q * x ∈ X) (S : C → C)
    (hS : ∀ x ∈ X, S x ∈ X ∧ g (S x) - S x = p * x)
    (B : Matrix (Fin r) (Fin r) C)
    (hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (w : Fin r → C) (hw : ∀ a, w a ∈ X) :
    ∃ y : Fin r → C, (∀ a, y a ∈ X) ∧
      ∀ a, g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a = p * w a := by
  let T : (Fin r → C) → (Fin r → C) := fun v a => -B.mulVec (fun b => g (S (v b))) a
  let v : ℕ → Fin r → C := fun n => T^[n] w
  have hvs : ∀ n, v (n + 1) = T (v n) := fun n => Function.iterate_succ_apply' T n w
  have hv : ∀ n a, v n a ∈ X := by
    intro n
    induction n with
    | zero => exact hw
    | succ n ih =>
      intro a
      rw [hvs]
      exact X.neg_mem (mulVec_mem X B hBX _ (fun b => hgX _ (hS _ (ih b)).1) a)
  have hqn : ∀ n : ℕ, ∀ x ∈ X, q ^ n * x ∈ X := by
    intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', mul_assoc]; exact hqX _ ih
  have hbd : ∀ n : ℕ, ∀ x ∈ X, ‖q ^ n * x‖ ≤ ‖q‖ ^ n := fun n x hx => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hX1 x hx)
  have hsum : ∀ a, Summable fun n => q ^ n * S (v n a) := fun a =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) hq1)
      fun n => hbd n _ (hS _ (hv n a)).1
  let y : Fin r → C := fun a => ∑' n, q ^ n * S (v n a)
  let Y : ℕ → Fin r → C := fun N a => ∑ n ∈ Finset.range N, q ^ n * S (v n a)
  have hY : ∀ a, Filter.Tendsto (fun N => Y N a) Filter.atTop (nhds (y a)) := fun a =>
    (hsum a).hasSum.tendsto_sum_nat
  refine ⟨y, fun a => hX.mem_of_tendsto (hY a) (Filter.Eventually.of_forall fun N =>
    X.sum_mem fun n _ => hqn n _ (hS _ (hv n a)).1), fun a => ?_⟩
  have hN : ∀ N, g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a
      = p * w a - p * (q ^ N * v N a) := by
    intro N
    induction N with
    | zero => simp [Y, v, Matrix.mulVec, dotProduct]
    | succ N ih =>
      have e : ∀ b, Y (N + 1) b = Y N b + q ^ N * S (v N b) := fun b => Finset.sum_range_succ _ _
      have e2 : (fun b => g (Y (N + 1) b))
          = (fun b => g (Y N b)) + q ^ N • fun b => g (S (v N b)) := by
        funext b; rw [e, map_add, map_mul, map_pow, hgq]; rfl
      rw [e2, e, map_add, map_mul, map_pow, hgq, Matrix.mulVec_add, Matrix.mulVec_smul, hvs]
      simp only [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ih + q ^ N * (hS _ (hv N a)).2
  have t1 : Filter.Tendsto (fun N => g (Y N a) - Y N a + p * q * B.mulVec (fun b => g (Y N b)) a)
      Filter.atTop (nhds (g (y a) - y a + p * q * B.mulVec (fun b => g (y b)) a)) := by
    refine (((hg.tendsto _).comp (hY a)).sub (hY a)).add (Filter.Tendsto.const_mul _ ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finset_sum _ fun b _ => ((hg.tendsto _).comp (hY b)).const_mul _
  have t0 : Filter.Tendsto (fun N => q ^ N * v N a) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun N => hbd N _ (hv N a))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  have t2 : Filter.Tendsto (fun N => p * w a - p * (q ^ N * v N a)) Filter.atTop
      (nhds (p * w a - p * 0)) := tendsto_const_nhds.sub (t0.const_mul p)
  rw [mul_zero, sub_zero] at t2
  simp only [hN] at t1
  exact tendsto_nhds_unique t1 t2

variable [IsUltrametricDist C]

theorem norm_zpow_sub_one_le (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CloseToUnitNorm.norm_zpow_sub_one_le ..)

end Abstract

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_lt_rho {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith

theorem rho_lt_one : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

theorem norm_root_sub_one {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) : ‖ζ - 1‖ = rho1 l := by
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  simpa [rho1] using this

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := by
  simp [inC, PadicComplex.coe_eq]

theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

theorem chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩

theorem norm_chiC_sub_one {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1

theorem exists_quot {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) {r : ℕ} (U : Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U - 1) a b‖ < rho1 l) (i : ℤ)
    {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) :
    ∃ (B : Matrix (Fin r) (Fin r) (PadicComplex l)),
      (∀ a b, ‖B a b‖ < 1) ∧ (∀ a b, B a b ∈ intC (Ks K j)) ∧
      chiC χ i g • U = 1 + (ζ - 1) • B := by
  have hz := norm_root_sub_one h
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  have hzp : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hz0
  have hc := norm_chiC_sub_one hj hg i
  have hc1 : ‖chiC χ i g‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hc.trans rho_lt_one).le le_rfl)
  let B : Matrix (Fin r) (Fin r) (PadicComplex l) := (ζ - 1)⁻¹ • (chiC χ i g • U - 1)
  have hB : ∀ a b, ‖B a b‖ < 1 := by
    intro a b
    have e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b
        + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b) := by
      simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
    rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc
      rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨B, hB, fun a b => ⟨?_, (hB a b).le⟩, ?_⟩
  · have m1 := (mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)
    have m2 := (mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))
    have m3 := (mem_inC_iff _ _).1 (hU a b).1
    rw [mem_inC_iff]
    simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]; abel

theorem twAct_sub {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ} {i : ℤ}
    {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l} {p : PadicComplex l}
    {B : Matrix (Fin r) (Fin r) (PadicComplex l)} (h : chiC χ i g • U g = 1 + p • B)
    (y : Fin r → PadicComplex l) (a : Fin r) :
    (twAct act χ i U g y - y) a
      = act g (y a) - y a + p * B.mulVec (fun b => act g (y b)) a := by
  rw [twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ intC F)
    (hy : y ∈ intC F) : x * y ∈ intC F :=
  ⟨(mem_inC_iff _ _).2 (mul_mem ((mem_inC_iff _ _).1 hx.1) ((mem_inC_iff _ _).1 hy.1)),
    by rw [norm_mul]; exact mul_le_one₀ hx.2 (norm_nonneg _) hy.2⟩

theorem exists_factor {F : IntermediateField ℚ_[l] (Om l)} {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (h1 : ∀ a b, ‖B a b‖ < 1)
    (hB : ∀ a b, B a b ∈ intC F) :
    ∃ (q : PadicComplex l) (B' : Matrix (Fin r) (Fin r) (PadicComplex l)), q ≠ 0 ∧ ‖q‖ < 1 ∧
      q ∈ intC F ∧ (∀ a b, B' a b ∈ intC F) ∧ B = q • B' := by
  have hq : ∃ q : PadicComplex l, q ≠ 0 ∧ ‖q‖ < 1 ∧ q ∈ inC F ∧ ∀ a b, ‖B a b‖ ≤ ‖q‖ := by
    by_cases h0 : B = 0
    · refine ⟨l, Nat.cast_ne_zero.2 hl.1.ne_zero, ?_, (mem_inC_iff _ _).2 (natCast_mem _ _),
        fun a b => by simp [h0]⟩
      rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.1.one_lt)
    · obtain ⟨a0, b0, hab⟩ : ∃ a b, B a b ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Matrix.ext hc)
      obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r × Fin r))
        (fun s => ‖B s.1 s.2‖) ⟨(a0, b0), Finset.mem_univ _⟩
      refine ⟨B s.1 s.2, ?_, h1 _ _, (hB _ _).1, fun a b => hs (a, b) (Finset.mem_univ _)⟩
      exact norm_pos_iff.1 ((norm_pos_iff.2 hab).trans_le (hs (a0, b0) (Finset.mem_univ _)))
  obtain ⟨q, hq0, hq1, hqF, hq⟩ := hq
  refine ⟨q, q⁻¹ • B, hq0, hq1, ⟨hqF, hq1.le⟩, fun a b => ⟨?_, ?_⟩, ?_⟩
  · exact (mem_inC_iff _ _).2 (mul_mem (inv_mem ((mem_inC_iff _ _).1 hqF))
      ((mem_inC_iff _ _).1 (hB a b).1))
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
      inv_mul_le_iff₀ (norm_pos_iff.2 hq0), mul_one]
    exact hq a b
  · rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]

theorem norm_le_one_of_Ohat (K : FinExt l) {x : PadicComplex l} (hx : x ∈ Ohat K) : ‖x‖ ≤ 1 :=
  closure_minimal (fun _ hy => hy.2) (isClosed_le continuous_norm continuous_const) hx

theorem perturbation : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  intro l hl act χ hact hχ K j hj g hg r U hU hU1 i
  obtain ⟨-, -, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1 := fun x hx => norm_le_one_of_Ohat K (hXO x hx)
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  constructor
  · intro y hy hfix
    have : NeZero l := ⟨hl.1.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
    obtain ⟨S, hS, -, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    refine inj_of_small (Xj K j) hX1 (act g) hgX (ζ - 1) q
      (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) hq0 hq1 (TateS.act_fix hact K hg.1 hqO.1) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
      (hlin _ (mul_mem_intC (TateS.zeta_sub_one_mem K hj.1 hζ) hqO))
      B' (fun a b => hmul _ (hB' a b)) y hy fun a => ?_
    rw [← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]
  · intro ζ hζ w hw
    obtain ⟨S, hS, -, -⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    obtain ⟨y, hy, he⟩ := surj_of_small (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1
      (act g) (AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).continuous hgX (ζ - 1) q hq1
      (TateS.act_fix hact K hg.1 hqO.1) (hmul _ hqO) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB' a b)) w hw
    refine ⟨y, hy, funext fun a => ?_⟩
    rw [twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.CycSeries
end

section
namespace GlobalTheory.UnitNormPowerSubOne

theorem norm_eq_one {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    have e : u + -(u - 1) = 1 := by ring
    rw [e, norm_one, norm_neg] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)
    have e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1 := by ring
    rw [e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul] at h1
    exact h1.trans (max_le le_rfl ih)

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  have hn := norm_eq_one u h
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u h n
  · have hp : u ^ n ≠ 0 := pow_ne_zero n hu
    have e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u h n

end GlobalTheory.UnitNormPowerSubOne
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycEigen

section Abstract

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_mulVec_le {r : ℕ} (B : Matrix (Fin r) (Fin r) C) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (v : Fin r → C) (a : Fin r) : ‖B.mulVec v a‖ ≤ c * ‖v‖ := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hB a b) (norm_le_pi_norm v b) (norm_nonneg _) hc

omit [IsUltrametricDist C] in
theorem mulVec_mem {r : ℕ} (X : AddSubgroup C) (B : Matrix (Fin r) (Fin r) C)
    (hB : ∀ a b, ∀ x ∈ X, B a b * x ∈ X) (v : Fin r → C) (hv : ∀ a, v a ∈ X) (a : Fin r) :
    B.mulVec v a ∈ X := by
  simp only [Matrix.mulVec, dotProduct]
  exact X.sum_mem fun b _ => hB a b _ (hv b)

omit [IsUltrametricDist C] in
theorem map_mulVec {r : ℕ} (X : AddSubgroup C) (O : Set C) (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X)
    (T : C → C) (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hB : ∀ a b, B a b ∈ O) (v : Fin r → C) (hv : ∀ a, v a ∈ X) :
    (fun a => T (B.mulVec v a)) = B.mulVec fun a => T (v a) := by
  let T' : X →+ C := AddMonoidHom.mk' (fun x => T x) fun x x' => hadd _ x.2 _ x'.2
  funext a
  have h := map_sum T' (fun b => (⟨B a b * v b, hOX _ (hB a b) _ (hv b)⟩ : X)) Finset.univ
  simp only [T', AddMonoidHom.mk'_apply, AddSubgroup.val_finset_sum] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  exact Finset.sum_congr rfl fun b _ => hlin _ (hB a b) _ (hv b)

theorem eq_zero_of_small {r : ℕ} (X : AddSubgroup C) (hX1 : ∀ x ∈ X, ‖x‖ ≤ 1) (O : Set C)
    (hOX : ∀ o ∈ O, ∀ x ∈ X, o * x ∈ X) (T : C → C) (hTX : ∀ x ∈ X, T x ∈ X)
    (hadd : ∀ x ∈ X, ∀ x' ∈ X, T (x + x') = T x + T x')
    (hlin : ∀ o ∈ O, ∀ x ∈ X, T (o * x) = o * T x)
    (B : Matrix (Fin r) (Fin r) C) (hBO : ∀ a b, B a b ∈ O) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hB : ∀ a b, ‖B a b‖ ≤ c) (y : Fin r → C) (hy : ∀ a, y a ∈ X)
    (h : y = B.mulVec fun a => T (y a)) : y = 0 := by
  have hBX : ∀ a b, ∀ x ∈ X, B a b * x ∈ X := fun a b => hOX _ (hBO a b)
  have h1 : ∀ (n : ℕ) (z : Fin r → C), (∀ a, z a ∈ X) →
      (∀ a, B.mulVec^[n] z a ∈ X) ∧ ‖B.mulVec^[n] z‖ ≤ c ^ n ∧
        (fun a => T (B.mulVec^[n] z a)) = B.mulVec^[n] fun a => T (z a) := by
    intro n z hz
    induction n with
    | zero => exact ⟨hz, (pi_norm_le_iff_of_nonneg (by simp)).2 fun a => by
        simpa using hX1 _ (hz a), rfl⟩
    | succ n ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      simp only [Function.iterate_succ_apply']
      refine ⟨mulVec_mem X B hBX _ i1, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_, ?_⟩
      · rw [pow_succ']
        exact (norm_mulVec_le B hc hB _ a).trans (mul_le_mul_of_nonneg_left i2 hc)
      · rw [map_mulVec X O hOX T hadd hlin B hBO _ i1, i3]
  have h2 : ∀ n : ℕ, ∃ z : Fin r → C, (∀ a, z a ∈ X) ∧ y = B.mulVec^[n] z := by
    intro n
    induction n with
    | zero => exact ⟨y, hy, rfl⟩
    | succ n ih =>
      obtain ⟨z, hz, e⟩ := ih
      refine ⟨fun a => T (z a), fun a => hTX _ (hz a), ?_⟩
      rw [Function.iterate_succ_apply', ← (h1 n z hz).2.2, ← e]
      exact h
  have h3 : ∀ n : ℕ, ‖y‖ ≤ c ^ n := fun n => by
    obtain ⟨z, hz, e⟩ := h2 n
    rw [e]; exact (h1 n z hz).2.1
  exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) h3)

theorem norm_zpow_sub_one_le (u : C) (hu : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  first
  | exact @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le
  | (apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le ..)

end Abstract

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_lt_rho {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith

theorem rho_lt_one : rho1 l < 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1]
  apply Real.rpow_lt_one_of_one_lt_of_neg h1
  exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

theorem norm_root_sub_one {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) : ‖ζ - 1‖ = rho1 l := by
  have := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  simpa [rho1] using this

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := by
  simp [inC, PadicComplex.coe_eq]

theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

theorem chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩

theorem norm_chiC_sub_one {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1

theorem exists_quot {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) {r : ℕ} (U : Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U - 1) a b‖ < rho1 l) (i : ℤ)
    {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ l) :
    ∃ (B : Matrix (Fin r) (Fin r) (PadicComplex l)) (c : ℝ), 0 ≤ c ∧ c < 1 ∧
      (∀ a b, ‖B a b‖ ≤ c) ∧ (∀ a b, B a b ∈ intC (Ks K j)) ∧
      chiC χ i g • U = 1 + (ζ - 1) • B := by
  have hz := norm_root_sub_one h
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  have hzp : 0 < ‖ζ - 1‖ := norm_pos_iff.2 hz0
  have hc := norm_chiC_sub_one hj hg i
  have hc1 : ‖chiC χ i g‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (chiC χ i g - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hc.trans rho_lt_one).le le_rfl)
  let B : Matrix (Fin r) (Fin r) (PadicComplex l) := (ζ - 1)⁻¹ • (chiC χ i g • U - 1)
  have hB : ∀ a b, ‖B a b‖ < 1 := by
    intro a b
    have e : B a b = (ζ - 1)⁻¹ * (chiC χ i g * (U - 1) a b
        + (chiC χ i g - 1) * (1 : Matrix (Fin r) (Fin r) (PadicComplex l)) a b) := by
      simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
    rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ hzp, mul_one, hz]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt (hU1 a b)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt hc
      rw [Matrix.one_apply]; split_ifs <;> simp
  refine ⟨B, ‖fun p : Fin r × Fin r => B p.1 p.2‖, norm_nonneg _,
    (pi_norm_lt_iff one_pos).2 fun p => hB _ _,
    fun a b => norm_le_pi_norm (fun p : Fin r × Fin r => B p.1 p.2) (a, b),
    fun a b => ⟨?_, (hB a b).le⟩, ?_⟩
  · have m1 := (mem_inC_iff _ _).1 (root_mem_inC K hj.1 h)
    have m2 := (mem_inC_iff _ _).1 (chiC_mem_inC χ i g (Ks K j))
    have m3 := (mem_inC_iff _ _).1 (hU a b).1
    rw [mem_inC_iff]
    simp only [B, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine mul_mem (inv_mem (sub_mem m1 (one_mem _))) (sub_mem (mul_mem m2 m3) ?_)
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp only [B, smul_smul, mul_inv_cancel₀ hz0, one_smul]; abel

theorem twAct_sub {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ} {i : ℤ}
    {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l} {p : PadicComplex l}
    {B : Matrix (Fin r) (Fin r) (PadicComplex l)} (h : chiC χ i g • U g = 1 + p • B)
    (y : Fin r → PadicComplex l) (a : Fin r) :
    (twAct act χ i U g y - y) a
      = act g (y a) - y a + p * B.mulVec (fun b => act g (y b)) a := by
  rw [twAct, ← Matrix.smul_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem act_inC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [ha.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx]

theorem ohat_norm (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have : closure (intC (Kinf K)) ⊆ {y : PadicComplex l | ‖y‖ ≤ 1} :=
    closure_minimal (fun _ h => h.2) (isClosed_le continuous_norm continuous_const)
  exact this hy

theorem twAct_fixed_eq_zero {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U g a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U g - 1) a b‖ < rho1 l) (i : ℤ)
    (y : Fin r → PadicComplex l) (hy : ∀ a, y a ∈ Xj K j) (hfix : twAct act χ i U g y = y) :
    y = 0 := by
  obtain ⟨-, -, hO, hmul, hstab, -⟩ :=
    GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  obtain ⟨S, hS, hadd, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
  obtain ⟨B, c, hc0, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
  have hBO' : ∀ a b, (-B) a b ∈ intC (Ks K j) := fun a b =>
    ⟨(mem_inC_iff _ _).2 (neg_mem ((mem_inC_iff _ _).1 (hBO a b).1)), by
      rw [Matrix.neg_apply, norm_neg]; exact (hBO a b).2⟩
  have hp : ζ - 1 ∈ intC (Ks K j) :=
    ⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)), by
      rw [norm_root_sub_one hζ]; exact rho_lt_one.le⟩
  have hp0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  refine eq_zero_of_small (Xj K j) (fun x hx => ohat_norm K (hO x hx)) _ hmul
    (fun x => S (act g x)) (fun x hx => (hS _ (hgX x hx)).1)
    (fun x hx x' hx' => by rw [map_add, hadd _ (hgX x hx) _ (hgX x' hx')])
    (fun o ho x hx => by rw [map_mul, act_inC hact hg.1 ho.1, hlin _ ho _ (hgX x hx)])
    (-B) hBO' hc0 hc1 (fun a b => by rw [Matrix.neg_apply, norm_neg]; exact hB a b) y hy ?_
  rw [← map_mulVec (Xj K j) _ hmul S hadd hlin (-B) hBO' _ fun a => hgX _ (hy a)]
  funext a
  have h1 : act g (y a) - y a = (ζ - 1) * (-B).mulVec (fun b => act g (y b)) a := by
    have := twAct_sub (act := act) hBe y a
    rw [hfix, sub_self, Pi.zero_apply] at this
    rw [Matrix.neg_mulVec, Pi.neg_apply]
    linear_combination -this
  have h2 := (hS _ (hy a)).2.2
  rw [h1, hlin _ hp _ (mulVec_mem (Xj K j) (-B) (fun a b => hmul _ (hBO' a b)) _
    (fun b => hgX _ (hy b)) a)] at h2
  exact (mul_left_cancel₀ hp0 h2).symm

end GlobalTheory.CycEigen
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycEigen

theorem aeval_eq_zero_of_eigenbasis {C : Type} [Field C] {r : ℕ} (A : Matrix (Fin r) (Fin r) C)
    (e : Fin r → Fin r → C) (he : LinearIndependent C e) (c : Fin r → C)
    (hc : ∀ k, A.mulVec (e k) = c k • e k) (P : Polynomial C) (hP : ∀ k, P.eval (c k) = 0) :
    Polynomial.aeval A P = 0 := by
  have h1 : ∀ k, (Polynomial.aeval A P).mulVec (e k) = 0 := by
    intro k
    have h2 : Matrix.toLinAlgEquiv' (Polynomial.aeval A P) (e k) = P.eval (c k) • e k := by
      rw [← Polynomial.aeval_algHom_apply]
      exact Module.End.aeval_apply_of_mem_apply_eq_smul (by simpa using hc k)
    rw [hP, zero_smul] at h2
    simpa using h2
  have hsp : Submodule.span C (Set.range e) = ⊤ :=
    he.span_eq_top_of_card_eq_finrank' (by simp)
  have h3 : Matrix.toLin' (Polynomial.aeval A P) = 0 :=
    LinearMap.ext_on_range hsp fun k => by simpa using h1 k
  simpa using h3

variable {l : ℕ} [Fact l.Prime]

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s :=
  IntermediateField.fixingSubgroup_antitone
    (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun (x : Om l) (hx : x ^ (l ^ s) = 1) =>
      (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _ : Ks K s ≤ Kinf K)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Ks K s from le_sup_left)

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow,
    (GlobalTheory.Cyc.cyc_basic l χ hχ).1, one_zpow]

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  have : χ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh
  simp [chiC, this]

theorem chiC_neg_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g : GQ l) :
    chiC χ (-j) g * chiC χ j g = 1 := by
  rw [chiC, chiC, ← map_mul, ← Units.val_mul, ← zpow_add]
  simp

theorem eigen_of_norm_le {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l) (hy1 : ∀ a, ‖y a‖ ≤ 1)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : chiC χ u g • (U g).mulVec y = y := by
  obtain ⟨hg, -, hU, -, hH, hU1⟩ := hF
  obtain ⟨hdec, hdir, -, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K m hm.1
  have hO : ∀ a, y a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act hact K (y a) (hy1 a)).1 fun h hh => ?_
    have := congrFun (hy h (hinf_le_gj K m hh)) a
    simpa [twAct, chiC_hinf hχ K u hh, hH h hh] using this
  choose y0 hy0 x hx hsum using fun a => hdec (y a) (hO a)
  have hfix : (fun a => act g (y0 a)) = y0 := funext fun a => act_inC hact hg.1 (hy0 a).1
  have hyx : y = y0 + x := funext hsum
  have hadd : twAct act χ u U g y = twAct act χ u U g y0 + twAct act χ u U g x := by
    have e : (fun a => act g (y a)) = (fun a => act g (y0 a)) + fun a => act g (x a) := by
      funext a; rw [hsum a, map_add]; rfl
    simp only [twAct]
    rw [e, Matrix.mulVec_add, smul_add]
  have hc : chiC χ u g ∈ intC (Ks K m) := ⟨chiC_mem_inC χ u g _, (norm_chiC hχ u g).le⟩
  have hX : ∀ a, twAct act χ u U g x a ∈ Xj K m := by
    intro a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact hmul _ hc _ ((Xj K m).sum_mem fun b _ =>
      hmul _ (hU g hg.1 a b) _ (hstab g (gj_le K m hg.1) _ (hx b)))
  have hK : ∀ a, twAct act χ u U g y0 a - y0 a ∈ inC (Ks K m) := by
    intro a
    rw [mem_inC_iff]
    simp only [twAct, hfix, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact sub_mem (mul_mem ((mem_inC_iff _ _).1 hc.1) (sum_mem fun b _ =>
      mul_mem ((mem_inC_iff _ _).1 (hU g hg.1 a b).1) ((mem_inC_iff _ _).1 (hy0 b).1)))
      ((mem_inC_iff _ _).1 (hy0 a).1)
  have hrel : ∀ a, twAct act χ u U g y0 a - y0 a = x a - twAct act χ u U g x a := by
    intro a
    have h1 := congrFun (hadd.symm.trans (hy g hg.1)) a
    rw [Pi.add_apply, hsum a] at h1
    linear_combination h1
  have hzero : ∀ a, twAct act χ u U g y0 a - y0 a = 0 := fun a =>
    hdir _ (hK a) _ ((Xj K m).sub_mem (hx a) (hX a)) 0 (by rw [pow_zero, one_mul]; exact hrel a)
  have hx0 : x = 0 := by
    refine twAct_fixed_eq_zero hact hχ hm hg U (hU g hg.1) hU1 u x hx ?_
    funext a
    exact (sub_eq_zero.1 ((hrel a).symm.trans (hzero a))).symm
  rw [hx0, add_zero] at hyx
  have h2 := hy g hg.1
  rw [hyx] at h2 ⊢
  rwa [twAct, hfix] at h2

theorem eigen_of_fixed {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : (U g).mulVec y = chiC χ (-u) g • y := by
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := (‖y‖ + 1)⁻¹) (by positivity) (norm_l_lt (l := l))
  have h1 : ∀ a, ‖(((l : PadicComplex l) ^ N) • y) a‖ ≤ 1 := by
    intro a
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    calc _ ≤ (‖y‖ + 1)⁻¹ * (‖y‖ + 1) :=
          mul_le_mul hN.le ((norm_le_pi_norm y a).trans (by linarith)) (norm_nonneg _)
            (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have h2 := eigen_of_norm_le hact hχ hm hF u _ h1 (by
    intro σ hσ
    have e : (fun a => act σ ((((l : PadicComplex l) ^ N) • y) a))
        = ((l : PadicComplex l) ^ N) • fun a => act σ (y a) := by
      funext a; simp
    have := hy σ hσ
    rw [twAct] at this ⊢
    rw [e, Matrix.mulVec_smul, smul_comm, this])
  rw [Matrix.mulVec_smul, smul_comm] at h2
  have h3 := smul_right_injective _ (pow_ne_zero N hl0) h2
  calc (U g).mulVec y = (chiC χ (-u) g * chiC χ u g) • (U g).mulVec y := by
        rw [chiC_neg_mul, one_smul]
    _ = _ := by rw [mul_smul, h3]

theorem aeval_prod_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  intro l _ act χ hact hχ K m r hm U g hF J ⟨e, u, he, hu, hfix⟩
  refine aeval_eq_zero_of_eigenbasis (U g) e he (fun k => chiC χ (-(u k)) g)
    (fun k => eigen_of_fixed hact hχ hm hF (u k) (e k) fun σ hσ => hfix σ hσ k) _ fun k => ?_
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_coe.1 (hu k)) (by simp)

end GlobalTheory.CycEigen
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  atlas_forward_decl GlobalTheory.CycEigen.aeval_prod_eq_zero
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

namespace GlobalTheory.CycCoinv

theorem prod_div {C ι : Type} [CommRing C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (b : C) (hb : b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (w : Fin r → C) (hw : ∀ a, w a ∈ O) (s : Finset ι) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      (aeval U (∏ u ∈ s, (X - Polynomial.C (f u)))).mulVec w
        = (∏ u ∈ s, (b - f u)) • w + (U.mulVec y - b • y) := by
  have hmv : ∀ y : Fin r → C, (∀ a, y a ∈ O) → ∀ a, U.mulVec y a ∈ O := fun y hy a => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun c _ => O.mul_mem (hU a c) (hy c)
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a => O.zero_mem, by simp⟩
  | insert u s hu ih =>
    obtain ⟨y, hy, he⟩ := ih
    refine ⟨(∏ u ∈ s, (b - f u)) • w + (U.mulVec y - f u • y), fun a => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact O.add_mem (O.mul_mem (O.prod_mem fun v _ => O.sub_mem hb (hf v)) (hw a))
        (O.sub_mem (hmv y hy a) (O.mul_mem (hf u) (hy a)))
    · rw [Finset.prod_insert hu, Finset.prod_insert hu, map_mul, ← Matrix.mulVec_mulVec, he,
        map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      module

theorem tors_int {C ι : Type} [Field C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (J : Finset ι) (hJ : aeval U (∏ u ∈ J, (X - Polynomial.C (f u))) = 0)
    (i : ι) (w w' : Fin r → C) (hw : ∀ a, w a ∈ O) (p : C) (hp : p ≠ 0)
    (h : U.mulVec w' - f i • w' = p • w) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      U.mulVec y - f i • y = (∏ u ∈ J.erase i, (f i - f u)) • w := by
  obtain ⟨y, hy, he⟩ := prod_div O U hU (f i) (hf i) f hf w hw (J.erase i)
  have hd : ∏ u ∈ J, (X - Polynomial.C (f u)) ∣
      (∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i)) := by
    by_cases hi : i ∈ J
    · rw [Finset.prod_erase_mul _ _ hi]
    · rw [Finset.erase_eq_of_notMem hi]; exact dvd_mul_right _ _
  obtain ⟨q, hq⟩ := hd
  have h0 : aeval U ((∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i))) = 0 := by
    rw [hq, map_mul, hJ, zero_mul]
  have h1 := congrArg (fun M => Matrix.mulVec M w') h0
  simp only [map_mul, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at h1
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, h, Matrix.mulVec_smul, smul_eq_zero] at h1
  have h2 := h1.resolve_left hp
  rw [h2] at he
  refine ⟨-y, fun a => O.neg_mem (hy a), ?_⟩
  rw [Matrix.mulVec_neg, eq_neg_of_add_eq_zero_left he.symm]
  module

variable {l : ℕ} [hl : Fact l.Prime]

noncomputable def fld (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

theorem mem_fld (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ fld F ↔ y ∈ inC F := by
  simp [fld, inC, PadicComplex.coe_eq]

noncomputable def intR (F : IntermediateField ℚ_[l] (Om l)) : Subring (PadicComplex l) where
  carrier := intC F
  mul_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (mul_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨(mem_fld F _).1 (one_mem _), by simp⟩
  add_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (add_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨(mem_fld F _).1 (zero_mem _), by simp⟩
  neg_mem' := fun {a} ha => ⟨(mem_fld F _).1 (neg_mem ((mem_fld F _).2 ha.1)), by simpa using ha.2⟩

theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] _ _ fun (x : Om l) hx =>
    (show ∃ j : ℕ, x ^ (l ^ j) = 1 from ⟨j, hx⟩)) _

theorem add_mem_Ohat (K : FinExt l) (j : ℕ) {y x : PadicComplex l} (hy : y ∈ intC (Ks K j))
    (hx : x ∈ Ohat K) : y + x ∈ Ohat K := by
  have hy' : y ∈ (intR (Kinf K)).topologicalClosure :=
    (intR (Kinf K)).le_topologicalClosure
      (show y ∈ intC (Kinf K) from ⟨Set.image_mono (Ks_le_Kinf K j) hy.1, hy.2⟩)
  have hx' : x ∈ (intR (Kinf K)).topologicalClosure := hx
  exact add_mem hy' hx'

theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

theorem algebraMap_mem (F : IntermediateField ℚ_[l] (Om l)) (t : ℚ_[l]) (ht : ‖t‖ ≤ 1) :
    algebraMap ℚ_[l] (PadicComplex l) t ∈ intR F :=
  ⟨⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩, by rwa [norm_algebraMap']⟩

theorem norm_l : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]

theorem quot_mem (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) {N : ℕ} (hN : 1 ≤ N) :
    (l : PadicComplex l) ^ N / (ζ - 1) ∈ intR (Ks K j) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.1.two_le
  have hz := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  refine ⟨(mem_fld _ _).1 (div_mem (pow_mem (natCast_mem _ _) _)
    (sub_mem ((mem_fld _ _).2 (root_mem_inC K hj h)) (one_mem _))), ?_⟩
  rw [norm_div, div_le_one (norm_pos_iff.2 hz0), norm_pow, norm_l, hz]
  calc ((l : ℝ)⁻¹) ^ N ≤ ((l : ℝ)⁻¹) ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1.le) hN
    _ = (l : ℝ) ^ (-1 : ℝ) := by rw [pow_one, Real.rpow_neg_one]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le h1.le
        simp only [tsub_self, pow_zero, one_mul]
        rw [le_div_iff₀ (by linarith)]
        linarith

theorem norm_chi {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) : ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hu : ‖(χ g : ℚ_[l]) - 1‖ < 1 := by
    rw [hg.2]
    exact zpow_lt_one_of_neg₀ h1 (by have := hj.1; omega)
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (χ g : ℚ_[l]) - 1) (y := 1)
    (by rw [norm_one]; exact hu.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this

theorem norm_prod_chi {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (J : Finset ℤ) (i : ℤ) :
    ‖∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u))‖
      = ((l : ℝ)⁻¹) ^ (∑ u ∈ J.erase i, (j + padicValInt l (u - i))) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun u hu => ?_
  have hne : u - i ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hu)
  have e : (χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)
      = (χ g : ℚ_[l]) ^ (-u) * ((χ g : ℚ_[l]) ^ (u - i) - 1) := by
    rw [mul_sub, ← zpow_add₀ (χ g).ne_zero, mul_one]
    congr 2; ring
  rw [e, norm_mul, norm_zpow, norm_chi hj hg, one_zpow, one_mul,
    GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l j hj _ hg.2 _ hne, inv_pow, ← zpow_natCast, ← zpow_neg]
  push_cast; rfl

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (IntermediateField.mem_fixingSubgroup_iff F g).1 hg x hx
  simp only []
  rw [hact.1, this]

theorem twAct_add (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ)
    {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l)
    (x y : Fin r → PadicComplex l) :
    twAct act χ i U g (x + y) = twAct act χ i U g x + twAct act χ i U g y := by
  rw [twAct, twAct, twAct, ← smul_add, ← Matrix.mulVec_add]
  congr 2
  funext a
  simp

theorem torsion_coinvariants : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  intro l hl act χ hact hχ K m r hm U g hF J hHT i w w' k hw hw' h
  have heig := GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame l act χ hact hχ K m r hm U g hF J hHT
  obtain ⟨hg, -, hUO, -, -, hU1⟩ := hF
  have hU : ∀ a b, U g a b ∈ intR (Ks K m) := hUO g hg.1
  obtain ⟨hdec, huniq, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K m hm.1
  have hgX := hstab g (IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K m) hg.1)
  choose w0 hw0 wx hwx hwe using fun a => hdec _ (hw a)
  choose v0 hv0 vx hvx hve using fun a => hdec _ (hw' a)
  obtain rfl : w = w0 + wx := funext hwe
  obtain rfl : w' = v0 + vx := funext hve
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 hl.1.ne_zero
  have hchi : ∀ u : ℤ, chiC χ u g = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ u) :=
    fun u => by simp [chiC]
  have hcO : ∀ u : ℤ, chiC χ u g ∈ intR (Ks K m) := fun u => by
    rw [hchi]
    exact algebraMap_mem _ _ (by rw [norm_zpow, norm_chi hm hg, one_zpow])
  have hcc : chiC χ i g * chiC χ (-i) g = 1 := by
    rw [hchi, hchi, ← map_mul, ← zpow_add₀ (χ g).ne_zero]; simp
  have htw : ∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ intR (Ks K m)) →
      twAct act χ i U g y - y = chiC χ i g • ((U g).mulVec y - chiC χ (-i) g • y) := by
    intro y hy
    have : (fun a => act g (y a)) = y := funext fun a => act_fix hact hg.1 (hy a).1
    rw [twAct, this, smul_sub, smul_smul, hcc, one_smul]
  have hlk : (l : PadicComplex l) ^ k ∈ intR (Ks K m) := pow_mem (natCast_mem _ _) _

  have h0 : twAct act χ i U g v0 - v0 = (l : PadicComplex l) ^ k • w0 := by
    rw [twAct_add] at h
    funext a
    have hO : (twAct act χ i U g v0 - v0) a - (l : PadicComplex l) ^ k * w0 a ∈ intR (Ks K m) := by
      rw [htw v0 hv0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact sub_mem (mul_mem (hcO i) (sub_mem (sum_mem fun b _ => mul_mem (hU a b) (hv0 b))
        (mul_mem (hcO _) (hv0 a)))) (mul_mem hlk (hw0 a))
    have hX : (l : PadicComplex l) ^ k * wx a - (twAct act χ i U g vx a - vx a) ∈ Xj K m := by
      refine sub_mem (hmul _ hlk _ (hwx a)) (sub_mem ?_ (hvx a))
      simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact hmul _ (hcO i) _ (sum_mem fun b _ => hmul _ (hU a b) _ (hgX _ (hvx b)))
    have := huniq _ hO.1 _ hX 0 (by
      have ha := congrFun h a
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
      linear_combination ha)
    exact sub_eq_zero.1 this
  set N := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN

  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  obtain ⟨yx, hyx, hyxe⟩ := (GlobalTheory.CycSeries.perturbation l act χ hact hχ K m hm g hg r U hU hU1 i).2 ζ hζ
    (((l : PadicComplex l) ^ N / (ζ - 1)) • wx)
    (fun a => hmul _ (quot_mem K hm.1 hζ (le_max_left _ _)) _ (hwx a))
  rw [smul_smul, mul_div_cancel₀ _ hz0] at hyxe

  have h1 : (U g).mulVec v0 - chiC χ (-i) g • v0
      = (chiC χ (-i) g * (l : PadicComplex l) ^ k) • w0 := by
    rw [mul_smul, ← h0, htw v0 hv0, smul_smul, mul_comm, hcc, one_smul]
  have hci : chiC χ (-i) g ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  obtain ⟨y, hy, hye⟩ := tors_int (intR (Ks K m)) (U g) hU (fun u => chiC χ (-u) g)
    (fun u => hcO _) J heig i w0 v0 hw0 _ (mul_ne_zero hci (pow_ne_zero _ hl0)) h1
  set β : ℚ_[l] := ∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)) with hβ
  have hβn := norm_prod_chi hm hg J i
  rw [← hβ] at hβn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hβ0 : β ≠ 0 := by
    rw [← norm_pos_iff, hβn]; positivity
  have hβe : ∏ u ∈ J.erase i, (chiC χ (-i) g - chiC χ (-u) g)
      = algebraMap ℚ_[l] (PadicComplex l) β := by
    simp only [hchi, hβ, map_prod, map_sub]
  have ht : algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) ∈ intR (Ks K m) := by
    apply algebraMap_mem
    rw [norm_div, div_le_one (norm_pos_iff.2 hβ0), hβn, norm_pow, Padic.norm_p]
    exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (le_max_right _ _)
  set t := algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) with htd
  have htβ : t * algebraMap ℚ_[l] (PadicComplex l) β = (l : PadicComplex l) ^ N := by
    rw [htd, ← map_mul, div_mul_cancel₀ _ hβ0, map_pow, map_natCast]
  have hy0 : ∀ a, ((t * chiC χ (-i) g) • y) a ∈ intR (Ks K m) := fun a =>
    mul_mem (mul_mem ht (hcO _)) (hy a)
  refine ⟨(t * chiC χ (-i) g) • y + yx, fun a => add_mem_Ohat K m (hy0 a) (hXO _ (hyx a)), ?_⟩
  have h2 : twAct act χ i U g ((t * chiC χ (-i) g) • y) - (t * chiC χ (-i) g) • y
      = (l : PadicComplex l) ^ N • w0 := by
    rw [htw _ hy0, Matrix.mulVec_smul, smul_comm (chiC χ (-i) g), ← smul_sub, hye, hβe,
      smul_smul, smul_smul, ← htβ]
    congr 1
    linear_combination t * algebraMap ℚ_[l] (PadicComplex l) β * hcc
  rw [twAct_add, smul_add, ← h2, ← hyxe]
  abel

end GlobalTheory.CycCoinv
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  atlas_forward_decl GlobalTheory.CycCoinv.torsion_coinvariants
end
