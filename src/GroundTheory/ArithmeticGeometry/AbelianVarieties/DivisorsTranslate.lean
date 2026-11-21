import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny

section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

theorem exists_eq_pow_of_le_one_iff {L : Type*} [Field L] (w v : Valuation L ℤᵐ⁰)
    (h : ∀ f, w f ≤ 1 ↔ v f ≤ 1) {π : L} (hπ : v π = exp (-1)) :
    ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v f ^ e := by
  have key : ∀ (u : Valuation L ℤᵐ⁰) (f : L), f ≠ 0 → (u f < 1 ↔ ¬ u f⁻¹ ≤ 1) :=
    fun u f hf => by rw [not_le, Valuation.one_lt_val_iff u (inv_ne_zero hf), inv_inv]
  have hlt : ∀ f : L, f ≠ 0 → (w f < 1 ↔ v f < 1) := fun f hf => by
    rw [key w f hf, key v f hf, h f⁻¹]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hwπ : w π < 1 := (hlt π hπ0).mpr (by rw [hπ, ← exp_zero, exp_lt_exp]; norm_num)
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
  obtain ⟨c, hwπc⟩ : ∃ c : ℤ, w π = exp c := ⟨_, (exp_log hwπ0).symm⟩
  have hc0 : c < 0 := by
    have := hwπ
    rwa [hwπc, ← exp_zero, exp_lt_exp] at this
  refine ⟨c.natAbs, by omega, fun f => ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, map_zero, zero_pow (by omega)]
  have hvf0 : v f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  obtain ⟨l, hvf⟩ : ∃ l : ℤ, v f = exp l := ⟨_, (exp_log hvf0).symm⟩
  have hg : v (f * π ^ l) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hvf, ← exp_zsmul, ← exp_add, ← exp_zero]
    congr 1
    simp
  have hwg : w (f * π ^ l) = 1 := by
    have hg0 : f * π ^ l ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hπ0)
    refine le_antisymm ((h _).mpr hg.le) (not_lt.mp fun hl => ?_)
    have := (hlt _ hg0).mp hl
    rw [hg] at this
    exact lt_irrefl _ this
  rw [map_mul, map_zpow₀, hwπc, ← exp_zsmul] at hwg
  rw [eq_inv_of_mul_eq_one_left hwg, hvf, ← exp_nsmul, ← exp_neg]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [Int.ofNat_natAbs_of_nonpos hc0.le]
  ring

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

section Poly

theorem algebraMap_C_functionField (c : F) :
    algebraMap F[X] W.toAffine.FunctionField (C c) = algebraMap F W.toAffine.FunctionField c :=
  (IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c).symm

theorem genY_sq_add : genY W ^ 2 + algebraMap F W.toAffine.FunctionField W.a₁ * genX W * genY W +
    algebraMap F W.toAffine.FunctionField W.a₃ * genY W = genX W ^ 3 +
      algebraMap F W.toAffine.FunctionField W.a₂ * genX W ^ 2 +
      algebraMap F W.toAffine.FunctionField W.a₄ * genX W +
      algebraMap F W.toAffine.FunctionField W.a₆ := by
  have e := (equation_iff _ _).mp (equation_gen W)
  simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using e

theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) =
      algebraMap F[X] W.toAffine.FunctionField p +
        algebraMap F[X] W.toAffine.FunctionField q * genY W := by
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

variable {W}

theorem valuation_poly_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (p : F[X]) : w (algebraMap F[X] W.toAffine.FunctionField p) ≤ 1 := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [algebraMap_C_functionField]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact (hF c hc).le
  | add p q hp hq => rw [map_add]; exact w.map_add_le hp hq
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← genX_eq]
    exact mul_le_one' ih hx

theorem valuation_poly_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) {p : F[X]} (hp : p ≠ 0) :
    w (algebraMap F[X] W.toAffine.FunctionField p) = exp (p.natDegree * k) := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have hlead : w (algebraMap F[X] W.toAffine.FunctionField
        (C p.leadingCoeff * X ^ p.natDegree)) = exp (d * k) := by
      rw [map_mul, map_pow, algebraMap_C_functionField, Valuation.map_mul, Valuation.map_pow,
        hF _ (leadingCoeff_ne_zero.mpr hp), ← genX_eq, hk, one_mul, ← exp_nsmul, h, nsmul_eq_mul]
    rw [← eraseLead_add_C_mul_X_pow p, map_add]
    rcases (eraseLead_natDegree_lt_or_eraseLead_eq_zero p) with hlt | he
    · by_cases he : p.eraseLead = 0
      · rw [he, map_zero, zero_add, hlead]
      · have hd : (p.eraseLead.natDegree : ℤ) < d := by exact_mod_cast h ▸ hlt
        rw [Valuation.map_add_eq_of_lt_right _ ?_, hlead]
        rw [hlead, ih _ (h ▸ hlt) he rfl, exp_lt_exp]
        nlinarith
    · rw [he, map_zero, zero_add, hlead]

theorem valuation_poly_le_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) (p : F[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    w (algebraMap F[X] W.toAffine.FunctionField p) ≤ exp (n * k) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [valuation_poly_of_one_lt w hF hk0 hk hp, exp_le_exp]
    have : (p.natDegree : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith

end Poly

section Gen

noncomputable def weierstrassB : F[X] := C W.a₁ * X + C W.a₃

noncomputable def weierstrassRHS : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

theorem genY_sq_add_weierstrassB :
    genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W =
      algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W) := by
  simp only [weierstrassB, weierstrassRHS, map_add, map_mul, map_pow,
    algebraMap_C_functionField, ← genX_eq]
  linear_combination genY_sq_add W

theorem natDegree_weierstrassRHS : (weierstrassRHS W).natDegree = 3 := by
  unfold weierstrassRHS; compute_degree!

theorem natDegree_weierstrassB_le : (weierstrassB W).natDegree ≤ 1 := by
  unfold weierstrassB; compute_degree

theorem weierstrassRHS_ne_zero : weierstrassRHS W ≠ 0 := by
  intro h
  have := natDegree_weierstrassRHS W
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

variable {W}

theorem valuation_genY_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) : ∃ m : ℤ, w (genY W) = exp m ∧ 2 * m = 3 * k := by
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  refine ⟨m, hm, ?_⟩
  have hwQ : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W)) = exp (3 * k) := by
    rw [valuation_poly_of_one_lt w hF hk0 hk (weierstrassRHS_ne_zero W), natDegree_weierstrassRHS]
    norm_num
  have hwB : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W)) ≤ exp (1 * k) :=
    valuation_poly_le_of_one_lt w hF hk0 hk _ (natDegree_weierstrassB_le W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hwBy : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) ≤
      exp (k + m) := by
    rw [Valuation.map_mul, hm]
    calc _ ≤ exp (1 * k) * exp m := mul_le_mul_left hwB _
      _ = exp (k + m) := by rw [← exp_add, one_mul]
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rcases lt_or_ge k m with hkm | hmk
  · have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
        w (genY W ^ 2) := by
      rw [hwy2]
      exact lt_of_le_of_lt hwBy (exp_lt_exp.mpr (by linarith))
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2, hwQ] at heq
    exact exp_inj.mp heq
  · exfalso
    have hle : w (genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) *
        genY W) ≤ exp (2 * k) :=
      w.map_add_le (by rw [hwy2, exp_le_exp]; linarith) (hwBy.trans (by rw [exp_le_exp]; linarith))
    rw [heq, hwQ, exp_le_exp] at hle
    linarith

theorem valuation_genY_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) : w (genY W) ≤ 1 := by
  by_contra hy
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  rw [not_le, hm, ← exp_zero, exp_lt_exp] at hy
  have hwB := valuation_poly_le_one w hF hx (weierstrassB W)
  have hwQ := valuation_poly_le_one w hF hx (weierstrassRHS W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
      w (genY W ^ 2) := by
    rw [Valuation.map_mul, hm, hwy2]
    calc _ ≤ 1 * exp m := mul_le_mul_left hwB _
      _ < exp (2 * m) := by rw [one_mul, exp_lt_exp]; linarith
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2] at heq
  rw [← heq, ← exp_zero, exp_le_exp] at hwQ
  linarith

theorem natDegree_norm_smul_basis_of_q_eq_zero {p : F[X]} :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) + (0 : F[X]) •
      AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * p.natDegree := by
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one, Algebra.norm_algebraMap,
    finrank_coordinateRing, natDegree_pow]

theorem natDegree_norm_smul_basis_of_p_eq_zero {q : F[X]} (hq : q ≠ 0) :
    (Algebra.norm F[X] ((0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * q.natDegree + 3 := by
  have h := degree_norm_smul_basis (W' := W.toAffine) 0 q
  rw [degree_eq_natDegree hq, degree_zero] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h, max_eq_right (by rw [two_nsmul, WithBot.bot_add]; exact bot_le)]
  norm_cast

theorem natDegree_norm_smul_basis_of_ne_zero {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h := degree_norm_smul_basis (W' := W.toAffine) p q
  rw [degree_eq_natDegree hq, degree_eq_natDegree hp] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h]
  norm_cast

theorem eq_valuationInfty_of_genX (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) = exp 2) : w = valuationInfty W := by
  obtain ⟨m, hm, hm3⟩ := valuation_genY_of_one_lt w hF two_pos hx
  have hm' : m = 3 := by linarith
  subst hm'
  have hA : ∀ a : W.toAffine.CoordinateRing,
      w (algebraMap _ W.toAffine.FunctionField a) =
        valuationInfty W (algebraMap _ W.toAffine.FunctionField a) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha]
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
    rw [algebraMap_smul_basis]
    rcases eq_or_ne q 0 with rfl | hq
    · have hp : p ≠ 0 := by rintro rfl; simp at ha
      rw [natDegree_norm_smul_basis_of_q_eq_zero, map_zero, zero_mul, add_zero,
        valuation_poly_of_one_lt w hF two_pos hx hp]
      push_cast; ring_nf
    · have hwQy : w (algebraMap F[X] W.toAffine.FunctionField q * genY W) =
          exp (2 * (q.natDegree : ℤ) + 3) := by
        rw [Valuation.map_mul, valuation_poly_of_one_lt w hF two_pos hx hq, hm, ← exp_add]
        ring_nf
      rcases eq_or_ne p 0 with rfl | hp
      · rw [natDegree_norm_smul_basis_of_p_eq_zero hq, map_zero, zero_add, hwQy]
        push_cast; ring_nf
      · rw [natDegree_norm_smul_basis_of_ne_zero hp hq]
        have hwP := valuation_poly_of_one_lt w hF two_pos hx hp
        rcases lt_or_gt_of_ne (show (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 3 by omega) with
          hlt | hlt
        · rw [Valuation.map_add_eq_of_lt_right _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwQy,
            max_eq_right (by omega)]
          push_cast; ring_nf
        · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwP,
            max_eq_left (by omega)]
          push_cast; ring_nf
  refine Valuation.ext fun f => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hspec := IsLocalization.mk'_spec W.toAffine.FunctionField a s
  have h1 := congrArg w hspec
  have h2 := congrArg (valuationInfty W) hspec
  rw [Valuation.map_mul, hA, hA] at h1
  rw [Valuation.map_mul] at h2
  have hvs : valuationInfty W (algebraMap _ W.toAffine.FunctionField
      (s : W.toAffine.CoordinateRing)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs)
  exact mul_right_cancel₀ hvs (h1.trans h2.symm)

theorem valuation_coordinateRing_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (a : W.toAffine.CoordinateRing) :
    w (algebraMap _ W.toAffine.FunctionField a) ≤ 1 := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [algebraMap_smul_basis]
  refine w.map_add_le (valuation_poly_le_one w hF hx p) ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (valuation_poly_le_one w hF hx q) (valuation_genY_le_one w hF hx)

end Gen

section CaseA

variable {W} [IsAlgClosed F] [W.IsElliptic]

theorem exists_eq_pow_valuation_of_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (hnt : ∃ f, f ≠ 0 ∧ w f ≠ 1) :
    ∃ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      (∀ a, a ∈ v.asIdeal ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1) ∧
      ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v.valuation W.toAffine.FunctionField f ^ e := by
  have hA := valuation_coordinateRing_le_one w hF hx
  let P : Ideal W.toAffine.CoordinateRing :=
    { carrier := {a | w (algebraMap _ W.toAffine.FunctionField a) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at ha ⊢
        calc _ ≤ 1 * w (algebraMap _ W.toAffine.FunctionField a) := mul_le_mul_left (hA c) _
          _ < 1 := by rwa [one_mul] }
  have hmem : ∀ a, a ∈ P ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1 := fun a => Iff.rfl
  have hone : ∀ a, a ∉ P → w (algebraMap _ W.toAffine.FunctionField a) = 1 :=
    fun a ha => le_antisymm (hA a) (not_lt.mp ha)
  have hPprime : P.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : W.toAffine.CoordinateRing) ∈ P := htop ▸ Submodule.mem_top
      rw [hmem, map_one, map_one] at h1
      exact lt_irrefl _ h1
    · by_contra hn
      push Not at hn
      rw [hmem, map_mul, Valuation.map_mul, hone a hn.1, hone b hn.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hP0 : P ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hwf⟩ := hnt
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
    apply hwf
    dsimp only at hf ⊢
    have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have ha : a ≠ 0 := by rintro rfl; exact hf (IsLocalization.mk'_zero _)
    have hnot : ∀ b : W.toAffine.CoordinateRing, b ≠ 0 → b ∉ P := fun b hb hbP =>
      hb ((Submodule.mem_bot _).mp (hbot ▸ hbP))
    have h1 := congrArg w (IsLocalization.mk'_spec W.toAffine.FunctionField a s)
    rw [Valuation.map_mul, hone _ (hnot _ hs), hone _ (hnot _ ha), mul_one] at h1
    exact h1
  let v : HeightOneSpectrum W.toAffine.CoordinateRing := ⟨P, hPprime, hP0⟩
  refine ⟨v, hmem, ?_⟩
  have hval_one : ∀ d : W.toAffine.CoordinateRing, d ∉ v.asIdeal →
      v.valuation W.toAffine.FunctionField (algebraMap _ _ d) = 1 := fun d hd => by
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hd
  have hle : ∀ f, w f ≤ 1 ↔ v.valuation W.toAffine.FunctionField f ≤ 1 := by
    intro f
    constructor
    · intro hwf
      by_contra hvf
      rw [not_le] at hvf
      have hf : f ≠ 0 := by rintro rfl; simp at hvf
      have hvf' : v.valuation W.toAffine.FunctionField f⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hvf).le
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f⁻¹ hvf'
      have hd : (d : W.toAffine.CoordinateRing) ∉ v.asIdeal := d.2
      have hvn : v.valuation W.toAffine.FunctionField (algebraMap _ _ n) < 1 := by
        rw [← hnd, Valuation.map_mul, hval_one _ hd, mul_one, map_inv₀]
        exact inv_lt_one_of_one_lt₀ hvf
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hvn
      have hwn := (hmem n).mp hvn
      rw [← hnd, Valuation.map_mul, hone _ hd, mul_one, map_inv₀] at hwn
      have : 1 < w f := by
        rwa [inv_lt_one₀ ((Valuation.pos_iff _).mpr hf)] at hwn
      exact absurd hwf (not_le.mpr this)
    · intro hvf
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f hvf
      have h1 := congrArg w hnd
      rw [Valuation.map_mul, hone _ d.2, mul_one] at h1
      exact h1 ▸ hA n
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer W.toAffine.FunctionField
  exact exists_eq_pow_of_le_one_iff w _ hle hπ

end CaseA

end GroundTheory.Arith.Abelian
end

section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

noncomputable def constPoint :
    W.toAffine.Point →+ (W.baseChange W.toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := W) (Algebra.ofId F W.toAffine.FunctionField)

theorem constPoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y),
      constPoint W (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

theorem map_constPoint (ψ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (R : W.toAffine.Point) : Point.map ψ (constPoint W R) = constPoint W R := by
  have h := Point.map_map (W' := W) (Algebra.ofId F W.toAffine.FunctionField) ψ R
  have e : ψ.comp (Algebra.ofId F W.toAffine.FunctionField) = Algebra.ofId F _ :=
    Subsingleton.elim _ _
  rw [e] at h
  exact h

omit [DecidableEq F] in
theorem map_genericPoint_eq (ψ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    [W.IsElliptic] :
    ∃ h, Point.map ψ (genericPoint W) = .some (ψ (genX W)) (ψ (genY W)) h :=
  ⟨_, rfl⟩

omit [DecidableEq F] in

theorem algHom_ext_gen {L : Type*} [Field L] [Algebra F L]
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[F] L} (hx : ψ₁ (genX W) = ψ₂ (genX W))
    (hy : ψ₁ (genY W) = ψ₂ (genY W)) : ψ₁ = ψ₂ := by
  have key := IntermediateField.algHom_ext_of_eq_adjoin F
    (S := (⊤ : IntermediateField F W.toAffine.FunctionField)) (adjoin_genX_genY W).symm
    (φ₁ := ψ₁.comp (IntermediateField.val ⊤)) (φ₂ := ψ₂.comp (IntermediateField.val ⊤)) (by
      rintro z (rfl | rfl)
      · exact hx
      · exact hy)
  refine AlgHom.ext fun z => ?_
  exact DFunLike.congr_fun key ⟨z, IntermediateField.mem_top⟩

variable [W.IsElliptic]

omit [DecidableEq F] in

theorem algHom_eq_of_map_genericPoint
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField}
    (h : Point.map ψ₁ (genericPoint W) = Point.map ψ₂ (genericPoint W)) : ψ₁ = ψ₂ := by
  obtain ⟨h₁, e₁⟩ := map_genericPoint_eq W ψ₁
  obtain ⟨h₂, e₂⟩ := map_genericPoint_eq W ψ₂
  rw [e₁, e₂, Point.some.injEq] at h
  exact algHom_ext_gen W h.1 h.2

omit [DecidableEq F] in
theorem map_id_genericPoint :
    Point.map (AlgHom.id F W.toAffine.FunctionField) (genericPoint W) = genericPoint W := rfl

omit [DecidableEq F] [W.IsElliptic] in

theorem exists_algebraMap_eq_of_isAlgebraic [IsAlgClosed F] {u : W.toAffine.FunctionField}
    (hu : IsAlgebraic F u) : ∃ c : F, algebraMap F W.toAffine.FunctionField c = u := by
  have hint := hu.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)
  exact ⟨c, hc⟩

theorem constPoint_ne_genericPoint (R : W.toAffine.Point) : constPoint W R ≠ genericPoint W := by
  cases R with
  | zero => exact fun h => Point.some_ne_zero _ (h.symm.trans (map_zero _))
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some W h
    rw [e, genericPoint, Ne, Point.some.injEq]
    intro hxy
    exact transcendental_genX W (hxy.1 ▸ isAlgebraic_algebraMap x)

theorem genericPoint_add_constPoint_ne_zero (R : W.toAffine.Point) :
    genericPoint W + constPoint W R ≠ 0 := by
  intro h
  apply constPoint_ne_genericPoint W (-R)
  rw [map_neg, eq_comm, ← add_eq_zero_iff_eq_neg]
  exact h

theorem exists_translate_eq (R : W.toAffine.Point) :
    ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
      (xOf _ (genericPoint W + constPoint W R)) (yOf _ (genericPoint W + constPoint W R)),
      genericPoint W + constPoint W R = .some _ _ h :=
  eq_some_xOf_yOf _ (genericPoint_add_constPoint_ne_zero W R)

theorem transcendental_xOf_translate [IsAlgClosed F] (R : W.toAffine.Point) :
    Transcendental F (xOf _ (genericPoint W + constPoint W R)) := by
  intro halg
  obtain ⟨h, e⟩ := exists_translate_eq W R
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic W halg
  set u := xOf _ (genericPoint W + constPoint W R)
  set v := yOf _ (genericPoint W + constPoint W R)
  have heq := (equation_iff _ _).mp h.1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
  have hvalg : IsAlgebraic F v := by
    refine ⟨X ^ 2 + C (W.a₁ * c + W.a₃) * X - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆), ?_, ?_⟩
    · intro h0
      have := congrArg natDegree h0
      rw [natDegree_zero] at this
      have h2 : (X ^ 2 + C (W.a₁ * c + W.a₃) * X -
          C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) : F[X]).natDegree = 2 := by
        compute_degree!
      omega
    · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hc]
      linear_combination heq
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isAlgebraic W hvalg
  have hcd : W.toAffine.Nonsingular c d := by
    have h' := h
    rw [← hc, ← hd] at h'
    exact (W.toAffine.baseChange_nonsingular (f := Algebra.ofId F W.toAffine.FunctionField)
      (algebraMap F _).injective c d).mp h'
  have hS : genericPoint W + constPoint W R = constPoint W (.some c d hcd) := by
    rw [e]
    obtain ⟨h'', e''⟩ := constPoint_some W hcd
    rw [e'']
    simp only [Point.some.injEq]
    exact ⟨hc.symm, hd.symm⟩
  apply constPoint_ne_genericPoint W (.some c d hcd - R)
  rw [map_sub, ← hS, add_sub_cancel_right]

noncomputable def translate [IsAlgClosed F] (R : W.toAffine.Point) :
    W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField :=
  liftPoint W (exists_translate_eq W R).choose.1 (transcendental_xOf_translate W R)

variable [IsAlgClosed F]

theorem map_translate_genericPoint (R : W.toAffine.Point) :
    Point.map (translate W R) (genericPoint W) = genericPoint W + constPoint W R := by
  rw [translate, map_liftPoint_genericPoint]
  exact (exists_translate_eq W R).choose_spec.symm

theorem translate_zero : translate W 0 = AlgHom.id F W.toAffine.FunctionField := by
  apply algHom_eq_of_map_genericPoint
  rw [map_translate_genericPoint, map_zero, add_zero, map_id_genericPoint]

theorem translate_comp_translate_neg (R : W.toAffine.Point) :
    (translate W R).comp (translate W (-R)) = AlgHom.id F W.toAffine.FunctionField := by
  apply algHom_eq_of_map_genericPoint
  rw [← Point.map_map, map_translate_genericPoint, map_add, map_translate_genericPoint,
    map_constPoint, add_assoc, ← map_add, add_neg_cancel, map_zero, add_zero, map_id_genericPoint]

theorem translate_translate_neg (R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    translate W R (translate W (-R) f) = f :=
  DFunLike.congr_fun (translate_comp_translate_neg W R) f

local notation "ι" => algebraMap F (WeierstrassCurve.Affine.FunctionField
  (WeierstrassCurve.toAffine W))

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_genX : valuationInfty W (genX W) = exp 2 := by
  have h := ordInfty_X W
  have h0 : genX W ≠ 0 := by
    intro h0
    change ordInfty W (genX W) = -2 at h
    rw [h0] at h
    simp [ordInfty] at h
  rw [valuationInfty_eq_exp W h0]
  change exp (-ordInfty W (genX W)) = _
  rw [show ordInfty W (genX W) = -2 from h]
  rfl

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_genY : valuationInfty W (genY W) = exp 3 := by
  have h := ordInfty_Y W
  rw [valuationInfty_eq_exp W (genY_ne_zero W)]
  change exp (-ordInfty W (genY W)) = _
  rw [show ordInfty W (genY W) = -3 from h]
  rfl

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_const_le (c : F) : valuationInfty W (ι c) ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
      ordInfty_algebraMap_const W hc, neg_zero, exp_zero]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_const_mul_le (c : F) {t : W.toAffine.FunctionField} {g : ℤᵐ⁰}
    (ht : valuationInfty W t ≤ g) : valuationInfty W (ι c * t) ≤ g := by
  rw [Valuation.map_mul]
  calc _ ≤ 1 * valuationInfty W t := mul_le_mul_left (valuationInfty_const_le W c) _
    _ ≤ g := by rw [one_mul]; exact ht

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_genX_sub_const (c : F) :
    valuationInfty W (genX W - ι c) = exp 2 := by
  rw [Valuation.map_sub_eq_of_lt_left _ ?_, valuationInfty_genX]
  rw [valuationInfty_genX]
  exact lt_of_le_of_lt (valuationInfty_const_le W c) (by rw [← exp_zero, exp_lt_exp]; norm_num)

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem genX_sub_const_ne_zero (c : F) : genX W - ι c ≠ 0 := by
  intro h
  have := valuationInfty_genX_sub_const W c
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

theorem translate_coords {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    translate W (.some xR yR hR) (genX W) =
        ((genY W - ι yR) / (genX W - ι xR)) ^ 2 + ι W.a₁ * ((genY W - ι yR) / (genX W - ι xR)) -
          ι W.a₂ - genX W - ι xR ∧
      translate W (.some xR yR hR) (genY W) =
        -((genY W - ι yR) / (genX W - ι xR) * (translate W (.some xR yR hR) (genX W) - genX W) +
          genY W) - ι W.a₁ * translate W (.some xR yR hR) (genX W) - ι W.a₃ := by
  have hne : genX W ≠ ι xR := fun h => genX_sub_const_ne_zero W xR (sub_eq_zero.mpr h)
  obtain ⟨hR', eR⟩ := constPoint_some W hR
  have hx : translate W (.some xR yR hR) (genX W) =
      xOf _ (genericPoint W + constPoint W (.some xR yR hR)) := liftPoint_genX _ _ _
  have hy : translate W (.some xR yR hR) (genY W) =
      yOf _ (genericPoint W + constPoint W (.some xR yR hR)) := liftPoint_genY _ _ _
  rw [eR, genericPoint, Point.add_of_X_ne hne] at hx hy
  simp only [xOf, yOf] at hx hy
  rw [slope_of_X_ne hne] at hx hy
  refine ⟨?_, ?_⟩
  · rw [hx]
    simp [addX, WeierstrassCurve.baseChange]
  · rw [hy, hx]
    simp [addY, negY, negAddY, addX, WeierstrassCurve.baseChange]

theorem valuationInfty_translate_genX_sub_lt {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    valuationInfty W (translate W (.some xR yR hR) (genX W) - ι xR) < 1 := by
  obtain ⟨hu, -⟩ := translate_coords W hR
  set u := translate W (.some xR yR hR) (genX W)
  set D := genX W - ι xR with hDdef
  have hD : D ≠ 0 := genX_sub_const_ne_zero W xR
  set ℓ := (genY W - ι yR) / D
  have hℓ : ℓ * D = genY W - ι yR := div_mul_cancel₀ _ hD
  have hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2) := by
    rw [hu]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    linear_combination (ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W
  have hN : valuationInfty W (ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2)) ≤ exp 3 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · exact valuationInfty_const_mul_le W _ (valuationInfty_genY W).le
    · exact valuationInfty_const_mul_le W _ (by rw [valuationInfty_genX, exp_le_exp]; norm_num)
    · exact (valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
  have hv := congrArg (valuationInfty W) hid
  rw [Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const] at hv
  rw [← hv] at hN
  by_contra hge
  rw [not_lt] at hge
  have : exp 2 ^ 2 ≤ exp 2 ^ 2 * valuationInfty W (u - ι xR) := le_mul_of_one_le_right' hge
  have h4 : (exp 2 : ℤᵐ⁰) ^ 2 = exp 4 := by rw [← exp_nsmul]; norm_num
  rw [h4] at this
  have := this.trans hN
  rw [exp_le_exp] at this
  norm_num at this

theorem valuationInfty_translate_genY_sub_lt {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    valuationInfty W (translate W (.some xR yR hR) (genY W) - ι yR) < 1 := by
  obtain ⟨hu, hvv⟩ := translate_coords W hR
  set u := translate W (.some xR yR hR) (genX W)
  set vv := translate W (.some xR yR hR) (genY W)
  set D := genX W - ι xR with hDdef
  have hD : D ≠ 0 := genX_sub_const_ne_zero W xR
  set ℓ := (genY W - ι yR) / D
  have hℓ : ℓ * D = genY W - ι yR := div_mul_cancel₀ _ hD
  have hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2) := by
    rw [hu]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    linear_combination (ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W
  have hid2 : D ^ 3 * (vv - ι yR) =
      (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
        ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
          W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W +
      ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * xR - W.a₁ * W.a₄ + W.a₂ * W.a₃ + 2 * W.a₂ * yR +
        3 * W.a₃ * xR + 6 * xR * yR) * genX W ^ 2 +
      ι (-2 * W.a₁ ^ 2 * xR * yR + 3 * W.a₁ * W.a₂ * xR ^ 2 + 2 * W.a₁ * W.a₄ * xR -
        W.a₁ * W.a₆ + 2 * W.a₁ * xR ^ 3 - 2 * W.a₁ * yR ^ 2 + 2 * W.a₂ * xR * yR + W.a₃ * W.a₄ -
        3 * W.a₃ * xR ^ 2 + 3 * W.a₄ * yR - 3 * xR ^ 2 * yR) * genX W +
      ι (W.a₁ ^ 2 * xR ^ 2 * yR - W.a₁ * W.a₂ * xR ^ 3 + 2 * W.a₁ * W.a₆ * xR - W.a₁ * xR ^ 4 +
        2 * W.a₁ * xR * yR ^ 2 - W.a₂ * xR ^ 2 * yR + W.a₃ * W.a₆ + W.a₃ * xR ^ 3 +
        3 * W.a₆ * yR + yR ^ 3) := by
    rw [hvv]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat] at hid ⊢
    linear_combination (-(D ^ 2 * u) + D ^ 2 * genX W) * hℓ +
      (-(genY W - ι yR) - ι W.a₁ * D) * hid +
      (ι W.a₁ * ι xR + ι W.a₃ + 2 * ι yR) * genY_sq_add W
  have hx2 : valuationInfty W (genX W) ≤ exp 5 := by
    rw [valuationInfty_genX, exp_le_exp]; norm_num
  have hM : valuationInfty W ((ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
        ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
          W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W +
      ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * xR - W.a₁ * W.a₄ + W.a₂ * W.a₃ + 2 * W.a₂ * yR +
        3 * W.a₃ * xR + 6 * xR * yR) * genX W ^ 2 +
      ι (-2 * W.a₁ ^ 2 * xR * yR + 3 * W.a₁ * W.a₂ * xR ^ 2 + 2 * W.a₁ * W.a₄ * xR -
        W.a₁ * W.a₆ + 2 * W.a₁ * xR ^ 3 - 2 * W.a₁ * yR ^ 2 + 2 * W.a₂ * xR * yR + W.a₃ * W.a₄ -
        3 * W.a₃ * xR ^ 2 + 3 * W.a₄ * yR - 3 * xR ^ 2 * yR) * genX W +
      ι (W.a₁ ^ 2 * xR ^ 2 * yR - W.a₁ * W.a₂ * xR ^ 3 + 2 * W.a₁ * W.a₆ * xR - W.a₁ * xR ^ 4 +
        2 * W.a₁ * xR * yR ^ 2 - W.a₂ * xR ^ 2 * yR + W.a₃ * W.a₆ + W.a₃ * xR ^ 3 +
        3 * W.a₆ * yR + yR ^ 3)) ≤ exp 5 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_
    · rw [Valuation.map_mul, valuationInfty_genY]
      have h1 : valuationInfty W (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
          ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
            W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) ≤ exp 2 :=
        Valuation.map_add_le _ (valuationInfty_const_mul_le W _ (valuationInfty_genX W).le)
          ((valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num))
      calc _ ≤ exp 2 * exp 3 := mul_le_mul_left h1 _
        _ = exp 5 := by rw [← exp_add]; norm_num
    · refine valuationInfty_const_mul_le W _ ?_
      rw [Valuation.map_pow, valuationInfty_genX, ← exp_nsmul, exp_le_exp]; norm_num
    · exact valuationInfty_const_mul_le W _ hx2
    · exact (valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
  have hv := congrArg (valuationInfty W) hid2
  rw [Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const] at hv
  rw [← hv] at hM
  by_contra hge
  rw [not_lt] at hge
  have : exp 2 ^ 3 ≤ exp 2 ^ 3 * valuationInfty W (vv - ι yR) := le_mul_of_one_le_right' hge
  have h6 : (exp 2 : ℤᵐ⁰) ^ 3 = exp 6 := by rw [← exp_nsmul]; norm_num
  rw [h6] at this
  have := this.trans hM
  rw [exp_le_exp] at this
  norm_num at this

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem algebraMap_XClass (x : F) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (XClass W.toAffine x) =
      genX W - ι x := by
  rw [← algebraMap_X_sub_C, ← IsScalarTower.algebraMap_apply, map_sub,
    algebraMap_C_functionField, ← genX_eq]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem algebraMap_YClass (y : F) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (YClass W.toAffine (C y)) =
      genY W - ι y := by
  rw [YClass, map_sub, map_sub]
  rfl

theorem valuationInfty_translate (R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    valuationInfty W (translate W R f) = valuationPoint W R f := by
  cases R with
  | zero =>
    rw [show (Point.zero : W.toAffine.Point) = 0 from rfl, translate_zero]
    rfl
  | some xR yR hR =>
    let w := (valuationInfty W).comap (translate W (.some xR yR hR)).toRingHom
    have hwapp : ∀ g, w g = valuationInfty W (translate W (.some xR yR hR) g) := fun g => rfl
    have hF : ∀ c : F, c ≠ 0 → w (ι c) = 1 := fun c hc => by
      rw [hwapp, AlgHom.commutes,
        valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
        ordInfty_algebraMap_const W hc, neg_zero, exp_zero]
    have hx : w (genX W) ≤ 1 := by
      rw [hwapp, ← sub_add_cancel (translate W (.some xR yR hR) (genX W)) (ι xR)]
      exact Valuation.map_add_le _ (valuationInfty_translate_genX_sub_lt W hR).le
        (valuationInfty_const_le W xR)
    obtain ⟨t, ht⟩ := exists_valuationPoint_eq_exp_neg_one W 0
    change valuationInfty W t = exp (-1) at ht
    have hinv := translate_translate_neg W (.some xR yR hR) t
    have ht0 : translate W (-(.some xR yR hR)) t ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hinv
      rw [← hinv, map_zero] at ht
      exact exp_ne_zero ht.symm
    have hwt : w (translate W (-(.some xR yR hR)) t) = exp (-1) := by rw [hwapp, hinv, ht]
    have hnt : ∃ g, g ≠ 0 ∧ w g ≠ 1 := ⟨_, ht0, by
      rw [hwt, Ne, ← exp_zero, exp_inj]; norm_num⟩
    obtain ⟨v, hv, e, he, hwe⟩ := exists_eq_pow_valuation_of_le_one w hF hx hnt
    have hvR : v = heightOneOfNonsingular hR := by
      have hle : XYIdeal W.toAffine xR (C yR) ≤ v.asIdeal := by
        rw [XYIdeal, Ideal.span_le]
        rintro _ (rfl | rfl)
        · rw [SetLike.mem_coe, hv, algebraMap_XClass, hwapp, map_sub, AlgHom.commutes]
          exact valuationInfty_translate_genX_sub_lt W hR
        · rw [SetLike.mem_coe, hv, algebraMap_YClass, hwapp, map_sub, AlgHom.commutes]
          exact valuationInfty_translate_genY_sub_lt W hR
      exact HeightOneSpectrum.ext ((isMaximal_XYIdeal hR.1).eq_of_le v.isPrime.ne_top hle).symm
    subst hvR
    have he1 : e = 1 := by
      have h1 := hwe (translate W (-(.some xR yR hR)) t)
      rw [hwt] at h1
      have hγ : (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField
          (translate W (-(.some xR yR hR)) t) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
      obtain ⟨g, hg⟩ : ∃ g : ℤ, (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField
          (translate W (-(.some xR yR hR)) t) = exp g := ⟨_, (exp_log hγ).symm⟩
      rw [hg, ← exp_nsmul, exp_inj, nsmul_eq_mul] at h1
      have hdvd : (e : ℤ) ∣ 1 := ⟨-g, by linarith⟩
      have := Int.eq_one_of_dvd_one (by positivity) hdvd
      exact_mod_cast this
    subst he1
    rw [← hwapp, hwe, pow_one]
    rfl

end GroundTheory.Arith.Abelian
end
