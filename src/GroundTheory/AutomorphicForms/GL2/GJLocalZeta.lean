import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.HaarCosets
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import GroundTheory.AutomorphicForms.GL2.GJInducedZeta

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Polynomial

def laurentSubalgebra : Subalgebra ℂ (RatFunc ℂ) :=
  Algebra.adjoin ℂ {RatFunc.X, RatFunc.X⁻¹}

theorem X_mem_laurentSubalgebra : (RatFunc.X : RatFunc ℂ) ∈ laurentSubalgebra :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem X_inv_mem_laurentSubalgebra : (RatFunc.X : RatFunc ℂ)⁻¹ ∈ laurentSubalgebra :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem C_mem_laurentSubalgebra (c : ℂ) : RatFunc.C c ∈ laurentSubalgebra := by
  rw [← RatFunc.algebraMap_eq_C]
  exact Subalgebra.algebraMap_mem _ c

theorem algebraMap_mem_laurentSubalgebra (P : ℂ[X]) :
    algebraMap ℂ[X] (RatFunc ℂ) P ∈ laurentSubalgebra := by
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · rw [RatFunc.algebraMap_C]
    exact C_mem_laurentSubalgebra a
  · rw [map_add]
    exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
    exact mul_mem h X_mem_laurentSubalgebra

theorem mem_laurentSubalgebra_iff {R : RatFunc ℂ} :
    R ∈ laurentSubalgebra ↔
      ∃ (P : ℂ[X]) (k : ℕ), R = algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ k := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · intro hR
    induction hR using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X, 0, by simp [RatFunc.algebraMap_X]⟩
      · exact ⟨1, 1, by simp⟩
    | algebraMap r =>
      exact ⟨Polynomial.C r, 0, by simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]⟩
    | add x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Polynomial.X ^ l + Q * Polynomial.X ^ k, k + l, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X]
      field_simp
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Q, k + l, ?_⟩
      rw [map_mul, pow_add]
      field_simp
  · rintro ⟨P, k, rfl⟩
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (algebraMap_mem_laurentSubalgebra P) (pow_mem X_inv_mem_laurentSubalgebra k)

theorem eval_div_algebraMap (P Q : ℂ[X]) {x : ℂ} (hx : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).eval (RingHom.id ℂ) x =
      P.eval x / Q.eval x := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hx
  set y := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q with hydef
  have hy : (y.denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    intro h0
    apply hx
    have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
      (RatFunc.denom_div_dvd P Q) h0
    simpa [Polynomial.eval₂_id] using this
  have hQd : ((algebraMap ℂ[X] (RatFunc ℂ) Q).denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    rw [RatFunc.denom_algebraMap]
    simp
  have hmul := RatFunc.eval_mul (RingHom.id ℂ) x hy hQd
  have hyQ : y * algebraMap ℂ[X] (RatFunc ℂ) Q = algebraMap ℂ[X] (RatFunc ℂ) P :=
    div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hQ)
  rw [hyQ, RatFunc.eval_algebraMap, RatFunc.eval_algebraMap] at hmul
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id] at hmul
  rw [eq_div_iff hx, ← hmul]

theorem eq_of_eval_eq {R₁ R₂ : RatFunc ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R₁.eval (RingHom.id ℂ) x = R₂.eval (RingHom.id ℂ) x) :
    R₁ = R₂ := by
  set Q : ℂ[X] := R₁.num * R₂.denom - R₂.num * R₁.denom with hQdef
  have hT : {x : ℂ | x ≠ 0 ∧ ‖x‖ < ε}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((ε / ((k : ℝ) + 2) : ℝ) : ℂ))
      ?_ ?_
    · intro a b hab
      have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
      have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
      have h1 : ε / ((a : ℝ) + 2) = ε / ((b : ℝ) + 2) := Complex.ofReal_injective hab
      rw [div_eq_div_iff ha.ne' hb.ne'] at h1
      have h2 : (b : ℝ) + 2 = (a : ℝ) + 2 := mul_left_cancel₀ hε.ne' h1
      have h3 : (a : ℝ) = b := by linarith
      exact_mod_cast h3
    · intro k
      have hk : 0 < ε / ((k : ℝ) + 2) := by positivity
      refine ⟨Complex.ofReal_ne_zero.2 hk.ne', ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      exact div_lt_self hε (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hroots : ({x | IsRoot R₁.denom x} ∪ {x | IsRoot R₂.denom x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _)).union
      (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _))
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (hT.sdiff hroots).mono ?_
    rintro x ⟨⟨hx0, hxε⟩, hxr⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Polynomial.IsRoot.def] at hxr
    have h1 := h x hx0 hxε
    simp only [RatFunc.eval, Polynomial.eval₂_id] at h1
    rw [div_eq_div_iff hxr.1 hxr.2] at h1
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hQdef, Polynomial.eval_sub,
      Polynomial.eval_mul, h1, sub_self]
  rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)), ← map_mul, ← map_mul]
  congr 1
  exact sub_eq_zero.1 hQ

section Ideal

variable {I : Submodule ℂ (RatFunc ℂ)}

theorem X_pow_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (k : ℕ) {R : RatFunc ℂ} (hR : R ∈ I) :
    RatFunc.X ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X, mul_assoc]
    exact hX _ ih

theorem X_inv_pow_mul_mem (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) (k : ℕ) {R : RatFunc ℂ}
    (hR : R ∈ I) : RatFunc.X⁻¹ ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X⁻¹, mul_assoc]
    exact hXinv _ ih

theorem algebraMap_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (P : ℂ[X]) {R : RatFunc ℂ}
    (hR : R ∈ I) : algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I := by
  suffices h : ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I from h R hR
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · intro R hR
    rw [RatFunc.algebraMap_C, ← RatFunc.smul_eq_C_mul]
    exact I.smul_mem a hR
  · intro R hR
    rw [map_add, add_mul]
    exact I.add_mem (hp R hR) (hq R hR)
  · intro R hR
    have : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ (k + 1)) * R =
        RatFunc.X * (algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ k) * R) := by
      rw [pow_succ, ← mul_assoc, map_mul _ (Polynomial.C a * Polynomial.X ^ k), RatFunc.algebraMap_X]
      ring
    rw [this]
    exact hX _ (h R hR)

theorem laurent_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I)
    (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) {L : RatFunc ℂ} (hL : L ∈ laurentSubalgebra)
    {R : RatFunc ℂ} (hR : R ∈ I) : L * R ∈ I := by
  obtain ⟨P, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  rw [div_eq_mul_inv, ← inv_pow, mul_assoc]
  exact algebraMap_mul_mem hX P (X_inv_pow_mul_mem hXinv k hR)

end Ideal

theorem dvd_of_inv_eq_laurent_div {P P' : ℂ[X]} (hP' : P'.eval 0 ≠ 0) {L : RatFunc ℂ}
    (hL : L ∈ laurentSubalgebra)
    (h : (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹ = L / algebraMap ℂ[X] (RatFunc ℂ) P) : P' ∣ P := by
  have hP'0 : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, inv_eq_zero] at h
    exact RatFunc.algebraMap_ne_zero hP'0 h
  obtain ⟨Q, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφP := RatFunc.algebraMap_ne_zero hP0
  have hφP' := RatFunc.algebraMap_ne_zero hP'0
  have heq : P * Polynomial.X ^ k = Q * P' := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h
    linear_combination h
  have hXP' : ¬ Polynomial.X ∣ P' := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hP'
  have hcop : IsCoprime P' (Polynomial.X ^ k) :=
    Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hXP'
  exact hcop.dvd_of_dvd_mul_right ⟨Q, by rw [heq, mul_comm]⟩

theorem eq_of_laurent_div_iff {P P' : ℂ[X]} (hP : P.eval 0 = 1) (hP' : P'.eval 0 = 1)
    (h : ∀ R : RatFunc ℂ, (∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P) ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P') : P = P' := by
  have h1 : P' ∣ P := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹).2
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP']; exact one_ne_zero) hL hLeq
  have h2 : P ∣ P' := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹).1
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP]; exact one_ne_zero) hL hLeq
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have hBA : B * A = 1 := by
    have : P * (B * A) = P * 1 := by
      rw [mul_one, ← mul_assoc, ← hB, ← hA]
    exact mul_left_cancel₀ hP0 this
  obtain ⟨a, -, ha⟩ := Polynomial.isUnit_iff.1 (IsUnit.of_mul_eq_one_right B hBA)
  have ha1 : a = 1 := by
    have := congrArg (Polynomial.eval 0) hA
    rw [Polynomial.eval_mul, ← ha, Polynomial.eval_C, hP, hP', one_mul] at this
    exact this.symm
  rw [hA, ← ha, ha1, map_one, mul_one]

theorem existsUnique_eq_laurent_div (I : Submodule ℂ (RatFunc ℂ))
    (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I)
    (h1 : (1 : RatFunc ℂ) ∈ I)
    (hD : ∃ D : ℂ[X], D ≠ 0 ∧ ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) :
    ∃! P : ℂ[X], P.eval 0 = 1 ∧
      ∀ R : RatFunc ℂ, R ∈ I ↔
        ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P := by
  classical
  obtain ⟨D, hD0, hDI⟩ := hD
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := RatFunc.algebraMap_ne_zero hD0

  let J : Ideal ℂ[X] :=
    { carrier := {Q | algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, add_div] at ha hb ⊢
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, zero_div]
        exact I.zero_mem
      smul_mem' := fun c {Q} hQ => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_div_assoc] at hQ ⊢
        exact algebraMap_mul_mem hX c hQ }
  have hJ : ∀ Q, Q ∈ J ↔
      algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I := fun Q => Iff.rfl
  set G := Submodule.IsPrincipal.generator J with hGdef
  have hGJ : G ∈ J := Submodule.IsPrincipal.generator_mem J
  have hdvd : ∀ Q, Q ∈ J ↔ G ∣ Q := fun Q => Submodule.IsPrincipal.mem_iff_generator_dvd J
  have hDJ : D ∈ J := by
    rw [hJ, div_self hφD]
    exact h1
  have hG0 : G ≠ 0 := by
    intro h
    have := (hdvd D).1 hDJ
    rw [h, zero_dvd_iff] at this
    exact hD0 this
  have hφG : algebraMap ℂ[X] (RatFunc ℂ) G ≠ 0 := RatFunc.algebraMap_ne_zero hG0
  have hGX : ¬ Polynomial.X ∣ G := by
    rintro ⟨G', hG'⟩
    have hG'0 : G' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hG'
      exact hG0 hG'
    have hG'J : G' ∈ J := by
      rw [hJ]
      have : algebraMap ℂ[X] (RatFunc ℂ) G' / algebraMap ℂ[X] (RatFunc ℂ) D =
          RatFunc.X⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D) := by
        rw [hG', map_mul, RatFunc.algebraMap_X]
        field_simp
      rw [this]
      exact hXinv _ hGJ
    have hle := Polynomial.natDegree_le_of_dvd ((hdvd G').1 hG'J) hG'0
    rw [hG', Polynomial.natDegree_mul Polynomial.X_ne_zero hG'0, Polynomial.natDegree_X] at hle
    omega

  have hchar : ∀ R, R ∈ I ↔ ∃ L ∈ laurentSubalgebra,
      R = algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D * L := by
    intro R
    constructor
    · intro hR
      obtain ⟨P, k, hPk⟩ := mem_laurentSubalgebra_iff.1 (hDI R hR)
      have hPJ : P ∈ J := by
        rw [hJ]
        have : algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) D =
            RatFunc.X ^ k * R := by
          rw [eq_div_iff (pow_ne_zero _ hXne)] at hPk
          rw [div_eq_iff hφD, ← hPk]
          ring
        rw [this]
        exact X_pow_mul_mem hX k hR
      obtain ⟨H, rfl⟩ := (hdvd P).1 hPJ
      refine ⟨algebraMap ℂ[X] (RatFunc ℂ) H / RatFunc.X ^ k,
        mem_laurentSubalgebra_iff.2 ⟨H, k, rfl⟩, ?_⟩
      rw [map_mul, eq_div_iff (pow_ne_zero _ hXne)] at hPk
      field_simp
      linear_combination hPk
    · rintro ⟨L, hL, rfl⟩
      rw [mul_comm]
      exact laurent_mul_mem hX hXinv hL hGJ

  obtain ⟨L1, hL1, h1eq⟩ := (hchar 1).1 h1
  obtain ⟨H, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL1
  have hDXk : D * Polynomial.X ^ k = G * H := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h1eq
    linear_combination h1eq
  have hGD : G ∣ D := by
    have hcop : IsCoprime G (Polynomial.X ^ k) :=
      Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hGX
    exact hcop.dvd_of_dvd_mul_right ⟨H, hDXk⟩
  obtain ⟨E, hE⟩ := hGD
  have hE0 : E ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hE
    exact hD0 hE
  obtain ⟨E₁, hE₁, hE₁X⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd E hE0 0
  simp only [map_zero, sub_zero] at hE₁ hE₁X
  set j := E.rootMultiplicity 0
  have hc : E₁.eval 0 ≠ 0 := by
    intro h
    apply hE₁X
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  set c := E₁.eval 0 with hcdef
  have hE₁0 : E₁ ≠ 0 := by
    rintro rfl
    exact hE₁X (dvd_zero _)
  have hφE₁ : algebraMap ℂ[X] (RatFunc ℂ) E₁ ≠ 0 := RatFunc.algebraMap_ne_zero hE₁0
  have hCc : RatFunc.C c ≠ 0 := by
    rw [← RatFunc.algebraMap_eq_C]
    exact (_root_.map_ne_zero _).2 hc
  have hGD' : algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D =
      (RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) E₁)⁻¹ := by
    rw [hE, hE₁, map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  have hφP : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) =
      (RatFunc.C c)⁻¹ * algebraMap ℂ[X] (RatFunc ℂ) E₁ := by
    rw [map_mul, RatFunc.algebraMap_C, map_inv₀]
  have hexists : (Polynomial.C c⁻¹ * E₁).eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ I ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) := by
    refine ⟨by rw [Polynomial.eval_mul, Polynomial.eval_C, ← hcdef, inv_mul_cancel₀ hc], ?_⟩
    intro R
    rw [hchar R, hφP, hGD']
    constructor
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * (RatFunc.X ^ j)⁻¹ * (RatFunc.C c)⁻¹,
        mul_mem (mul_mem hL (by rw [← inv_pow]; exact pow_mem X_inv_mem_laurentSubalgebra j))
          (by rw [← map_inv₀]; exact C_mem_laurentSubalgebra _), ?_⟩
      field_simp
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * RatFunc.X ^ j * RatFunc.C c,
        mul_mem (mul_mem hL (pow_mem X_mem_laurentSubalgebra j)) (C_mem_laurentSubalgebra c), ?_⟩
      field_simp
  refine ⟨Polynomial.C c⁻¹ * E₁, hexists, ?_⟩
  rintro P' ⟨hP'0, hP'⟩
  exact (eq_of_laurent_div_iff hexists.1 hP'0 fun R => (hexists.2 R).symm.trans (hP' R)).symm

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory

section Extension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}

theorem exists_extend_dual (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (ι : Representation.IntertwiningMap ρ τ) (hι : Function.Injective ι) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {ℓ : Module.Dual ℂ V}
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    ∃ lam : Module.Dual ℂ U, (∀ k ∈ K, ∀ x, lam (τ k x) = lam x) ∧ ∀ v, lam (ι v) = ℓ v := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (fixedMap ρ ι K)
    (LinearMap.ker_eq_bot.2 (fixedMap_injective ρ hι))
  refine ⟨ℓ ∘ₗ (fixedVectors ρ K).subtype ∘ₗ r ∘ₗ fixedProj τ hτ hKc hKo, fun k hk x => ?_,
    fun v => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [fixedProj_apply_act hτ hKc hKo hk]
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [fixedProj_map hKc hKo hρ hτ ι v]
    have h1 : r (fixedMap ρ ι K (fixedProj ρ hρ hKc hKo v)) = fixedProj ρ hρ hKc hKo v := by
      rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
    rw [h1]

    have hker : ∀ y ∈ coinvariantsKer ρ K, ℓ y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hy
      rintro _ ⟨k, rfl⟩
      simp [hℓ k.1.1 k.1.2 k.2]
    have := hker _ (sub_fixedProj_mem hρ hKc hKo v)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

end Extension

section Decomposition

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (F n) in

theorem exists_reps_congruenceSubgroup (m : ℕ) :
    ∃ R : Finset (GL (Fin n) F), (∀ x ∈ R, x ∈ integralGL F n) ∧
      ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m := by
  classical
  set K₀ := integralGL F n
  set K := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F),
    ?_, fun k hk => ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q).2
  · refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨k, hk⟩ : K₀) :
      K₀ ⧸ K.subgroupOf K₀))
    exact Subgroup.mem_subgroupOf.1 h

theorem exists_eval_decomposition (hσ : IsSmooth σ) {m : ℕ} {R : Finset (GL (Fin n) F)}
    (hR₀ : ∀ x ∈ R, x ∈ integralGL F n)
    (hR : ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m)
    (lam : Module.Dual ℂ (parabolicIndSpace F n β σ)) :
    ∃ ℓ : GL (Fin n) F → Module.Dual ℂ W,
      (∀ x, ℓ x ∈ fixedVectors (Representation.dual σ)
        ((congruenceSubgroup F n m).subgroupOf (levi F n β))) ∧
      ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
        lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) := by
  classical
  have : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set K := congruenceSubgroup F n m
  set KM : Subgroup (levi F n β) := K.subgroupOf (levi F n β)
  have hKMc : IsCompact (KM : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)
  have hKMo : IsOpen (KM : Set (levi F n β)) :=
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  set e := fixedProj σ hσ hKMc hKMo

  let E : fixedVectors (parabolicInd F n β σ) K →ₗ[ℂ] (R → W) :=
    LinearMap.pi fun x : R =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) (x : GL (Fin n) F)) ∘ₗ
        (parabolicIndSpace F n β σ).subtype ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype
  have hE : ∀ ψ, E ψ = 0 → ψ = 0 := by
    intro ψ hψ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨x, hxR, hxk⟩ := hR k hk
    have h0 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x = 0 := by
      have := congrFun hψ ⟨x, hxR⟩
      simpa [E] using this
    have hfix := ψ.2 (x⁻¹ * k) hxk
    have h1 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * k) =
        ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * x) := by
      have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (p * x)) hfix
      simp only [coe_indRep_apply] at this
      rw [← this, mul_assoc, mul_inv_cancel_left]
    rw [h1, ((ψ : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ x), h0]
    simp
  have hker : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot'.2 hE
  obtain ⟨E', hE'⟩ := LinearMap.exists_leftInverse_of_injective (K := ℂ)
    (V := fixedVectors (parabolicInd F n β σ) K) (V' := R → W) E hker
  let L := lam ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype ∘ₗ E'
  refine ⟨fun x => if hx : x ∈ R then
      L ∘ₗ LinearMap.single ℂ (fun _ : R => W) ⟨x, hx⟩ ∘ₗ (fixedVectors σ KM).subtype ∘ₗ e
    else 0, fun x => ?_, fun ψ hψ => ?_⟩
  · by_cases hx : x ∈ R
    · dsimp only
      rw [dif_pos hx, mem_fixedVectors_dual]
      intro k hk w
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [fixedProj_apply_act hσ hKMc hKMo hk]
    · dsimp only
      rw [dif_neg hx]
      exact zero_mem _
  · have hval : ∀ x ∈ R, ((fixedProj σ hσ hKMc hKMo ((ψ : GL (Fin n) F → W) x) :
        fixedVectors σ KM) : W) = (ψ : GL (Fin n) F → W) x := fun x hx =>
      fixedProj_apply_of_mem hσ hKMc hKMo
        (apply_mem_fixedVectors (f := ⟨ψ, hψ⟩) (hR₀ x hx))
    have hEψ : E ⟨ψ, hψ⟩ = ∑ x : R, LinearMap.single ℂ (fun _ : R => W) x
        ((ψ : GL (Fin n) F → W) x) := by
      funext y
      simp [E, Finset.sum_apply, Pi.single_apply]
    have hlam : lam ψ = L (E ⟨ψ, hψ⟩) := by
      simp only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← LinearMap.comp_apply E' E, hE', LinearMap.id_apply]
    rw [hlam, hEψ, map_sum, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hval x x.2]

end Decomposition

section Integral

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem integral_mul_coeff_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g) :
    ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ =
      ∑ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
  classical
  let Ko : OpenSubgroup (GL (Fin n) F) := ⟨K, hKo⟩
  have hφk : ∀ k ∈ K, parabolicInd F n β σ k φ = φ := fun k hk => hφ k hk

  have hfin : (QuotientGroup.mk '' tsupport h : Set (GL (Fin n) F ⧸ K)).Finite :=
    finite_image_mk_tsupport Ko hh

  have hL : ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * lam (parabolicInd F n β σ (g * k) φ) = h g * lam (parabolicInd F n β σ g φ)
    rw [hhr k hk, map_mul, Module.End.mul_apply, hφk k hk]
  have hR : ∀ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * ℓ x ((φ : GL (Fin n) F → W) (x * (g * k))) = h g * ℓ x ((φ : GL (Fin n) F → W) (x * g))
    have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (x * g)) (hφk k hk)
    simp only [coe_indRep_apply] at this
    rw [hhr k hk, ← mul_assoc, this]

  set ψ : parabolicIndSpace F n β σ := ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out • parabolicInd F n β σ c.out φ
    with hψdef
  have hψsupp : (Function.support fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ).Finite :=
    hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
      QuotientGroup.out_eq' c⟩
  have hψK : ψ ∈ fixedVectors (parabolicInd F n β σ) K := by
    intro k hk
    rw [hψdef, map_finsum (parabolicInd F n β σ k) hψsupp]
    have hterm : ∀ c : GL (Fin n) F ⧸ K,
        parabolicInd F n β σ k (h c.out • parabolicInd F n β σ c.out φ) =
        (fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ)
          (MulAction.toPerm k c) := by
      intro c
      have hmk : (QuotientGroup.mk (k * c.out) : GL (Fin n) F ⧸ K) = MulAction.toPerm k c := by
        show QuotientGroup.mk (k * c.out) = k • c
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl
      obtain ⟨j, hj, hjeq⟩ : ∃ j ∈ K, k * c.out = (MulAction.toPerm k c).out * j := by
        refine ⟨((MulAction.toPerm k c).out)⁻¹ * (k * c.out), ?_, by group⟩
        have := QuotientGroup.eq.1 ((QuotientGroup.out_eq' (MulAction.toPerm k c)).trans hmk.symm)
        simpa using this
      have hhc : h c.out = h (MulAction.toPerm k c).out := by
        rw [← hhl k hk c.out, hjeq, hhr j hj]
      dsimp only
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hjeq, map_mul, Module.End.mul_apply,
        hφk j hj, hhc]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ)

  have h1 : lam ψ = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    rw [hψdef, map_finsum lam hψsupp]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) =
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    let ev : parabolicIndSpace F n β σ →ₗ[ℂ] W :=
      LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) x ∘ₗ
        (parabolicIndSpace F n β σ).subtype
    have hev : (ψ : GL (Fin n) F → W) x = ev ψ := rfl
    rw [hev, hψdef, map_finsum ev hψsupp, map_finsum (ℓ x)]
    · refine finsum_congr fun c => ?_
      simp [ev, coe_indRep_apply]
    · exact hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
        QuotientGroup.out_eq' c⟩
  rw [hL, ← h1, hdec ψ hψK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hR x hx, h2 x hx]

end Integral

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory Polynomial
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

section Shells

theorem measurableSet_shell (k : ℤ) : MeasurableSet {g : GL (Fin n) F | ordDet g = k} :=
  (isClopen_shell F n k).isOpen.measurableSet

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem pairwise_disjoint_shell :
    Pairwise (Function.onFun Disjoint fun k : ℤ => {g : GL (Fin n) F | ordDet g = k}) := by
  intro a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab ?_
  exact ha.symm.trans hb

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem iUnion_shell : (⋃ k : ℤ, {g : GL (Fin n) F | ordDet g = k}) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨ordDet g, rfl⟩

theorem hasSum_integral_shell (μ : Measure (GL (Fin n) F)) {H : GL (Fin n) F → ℂ}
    (hH : Integrable H μ) :
    HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, H g ∂μ) (∫ g, H g ∂μ) := by
  have := hasSum_integral_iUnion (μ := μ) (f := H) measurableSet_shell pairwise_disjoint_shell
    (by rw [iUnion_shell]; exact hH.integrableOn)
  rwa [iUnion_shell, Measure.restrict_univ] at this

theorem lintegral_eq_tsum_shell (μ : Measure (GL (Fin n) F)) (H : GL (Fin n) F → ℝ≥0∞) :
    ∫⁻ g, H g ∂μ = ∑' k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, H g ∂μ := by
  rw [← lintegral_iUnion measurableSet_shell pairwise_disjoint_shell, iUnion_shell,
    Measure.restrict_univ]

end Shells

section Bound

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem lintegral_norm_mul_coeff_le (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    (hlam : ∀ k ∈ K, ∀ ψ, lam (parabolicInd F n β σ k ψ) = lam ψ)
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g)
    (hhf : Integrable (fun g => ‖h g * lam (parabolicInd F n β σ g φ)‖) μ)
    (hint : ∀ x ∈ R, Integrable (fun g => ‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖) μ) :
    ∫⁻ g, ENNReal.ofReal ‖h g * lam (parabolicInd F n β σ g φ)‖ ∂μ ≤
      ∑ x ∈ R, ∫⁻ g, ENNReal.ofReal (‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖) ∂μ := by
  classical
  set f : GL (Fin n) F → ℂ := fun g => lam (parabolicInd F n β σ g φ) with hfdef
  have hfl : ∀ k ∈ K, ∀ g, f (k * g) = f g := fun k hk g => by
    simp only [f, map_mul, Module.End.mul_apply, hlam k hk]
  have hfr : ∀ k ∈ K, ∀ g, f (g * k) = f g := fun k hk g => by
    simp only [f, map_mul, Module.End.mul_apply]
    rw [show parabolicInd F n β σ k φ = φ from hφ k hk]

  set u : GL (Fin n) F → ℂ := fun g => if h g * f g = 0 then 0 else
    (starRingEnd ℂ) (h g * f g) / (‖h g * f g‖ : ℂ) with hudef
  have hu1 : ∀ g, ‖u g‖ ≤ 1 := fun g => by
    simp only [u]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h0)]
  have huf : ∀ g, u g * h g * f g = (‖h g * f g‖ : ℂ) := fun g => by
    simp only [u]
    split_ifs with h0
    · simp [h0]
    · have hne : ((‖h g * f g‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
      rw [mul_assoc, div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc, div_self hne,
        mul_one]
  set h' : GL (Fin n) F → ℂ := fun g => u g * h g with hh'def
  have hh' : HasCompactSupport h' := hh.mul_left
  have hul : ∀ k ∈ K, ∀ g, u (k * g) = u g := fun k hk g => by
    simp only [u, hhl k hk, hfl k hk]
  have hur : ∀ k ∈ K, ∀ g, u (g * k) = u g := fun k hk g => by
    simp only [u, hhr k hk, hfr k hk]
  have key := integral_mul_coeff_eq μ hKc hKo hφ hdec hh'
    (fun k hk g => by simp only [h', hul k hk, hhl k hk])
    (fun k hk g => by simp only [h', hur k hk, hhr k hk])

  have hL : ∫ g, h' g * f g ∂μ = ((∫ g, ‖h g * f g‖ ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
      simp only [h']; exact huf g)
  have hineq : ∫ g, ‖h g * f g‖ ∂μ ≤
      ∑ x ∈ R, ∫ g, ‖h g‖ * ‖ℓ x ((φ : GL (Fin n) F → W) (x * g))‖ ∂μ := by
    have h1 : ‖∫ g, h' g * f g ∂μ‖ = ∫ g, ‖h g * f g‖ ∂μ := by
      rw [hL, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun g => norm_nonneg _)]
    rw [← h1, key]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun g => norm_nonneg _) (hint x hx)
      (Filter.Eventually.of_forall fun g => ?_))
    simp only [h', norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (hu1 g))
      (norm_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hhf (Filter.Eventually.of_forall fun g => norm_nonneg _)]
  rw [Finset.sum_congr rfl fun x hx => (ofReal_integral_eq_lintegral_ofReal (hint x hx)
    (Filter.Eventually.of_forall fun g => mul_nonneg (norm_nonneg _) (norm_nonneg _))).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun x _ => integral_nonneg fun g =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hineq

end Bound

section Core

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem isLocallyConstant_of_mul_right {γ : Type*} {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {f : GL (Fin n) F → γ}
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (K : Set (GL (Fin n) F)),
    hKo.preimage (continuous_const.mul continuous_id), by simp [K.one_mem], fun y hy => ?_⟩
  have := hf x (x⁻¹ * y) hy
  rwa [mul_inv_cancel_left] at this

theorem exists_zeta_core [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g s ∂μ = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, -, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hπ.1
  have := hσirr
  obtain ⟨s₀, D, hD0, hJ⟩ := exists_inducedZeta (β := β) hσs hσc μ
  refine ⟨s₀, D, hD0, fun Φ hΦ v ℓ hℓ => ?_⟩

  obtain ⟨m₀, hm₀⟩ := hΦ.exists_congruence_invariant
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ.1 v).mem_nhds (one_mem (stabilizerOf π v)))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))
  set m := max m₀ (max m₁ m₂) with hmdef
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hK0 : ∀ k ∈ K, k ∈ integralGL F n := fun k hk => congruenceSubgroup_le F n m hk
  have hvK : ∀ k ∈ K, π k v = v := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)
  have hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun k hk =>
    hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)

  obtain ⟨lam, hlamK, hlam⟩ := exists_extend_dual hπ.1 (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK
  obtain ⟨R, hR₀, hR⟩ := exists_reps_congruenceSubgroup F n m
  obtain ⟨ℓx, hℓxK, hdec⟩ := exists_eval_decomposition hσs hR₀ hR lam
  set φ : parabolicIndSpace F n β σ := ι v with hφdef
  have hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K := fun k hk => by
    rw [hφdef, ← ι.isIntertwining, hvK k hk]
  have hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ) := fun g => by
    rw [matrixCoeff, ← hlam, hφdef, ι.isIntertwining]
  have hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ) := fun x =>
    mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)

  have hJx := fun x : GL (Fin n) F => hJ
    (fun X => Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X))
    (hΦ.comp_mul_left x⁻¹) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)
  choose hJint N P hJeq using hJx

  set T : GL (Fin n) F → ℂ → GL (Fin n) F → ℂ := fun x s g =>
    Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓx x ((φ : GL (Fin n) F → W) (x * g))
    with hTdef
  have hTJ : ∀ x ∈ R, ∀ s g, T x s g = (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) (x * g) := by
    intro x hx s g
    simp only [T]
    rw [detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul, Units.val_mul, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hTint : ∀ x ∈ R, ∀ s : ℂ, s₀ < s.re → Integrable (T x s) μ := by
    intro x hx s hs
    exact ((hJint x s hs).comp_mul_left x).congr
      (Filter.Eventually.of_forall fun g => (hTJ x hx s g).symm)
  have hTeq : ∀ x ∈ R, ∀ s, ∫ g, T x s g ∂μ = ∫ g,
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F)) *
        detPow g s * ℓx x ((φ : GL (Fin n) F → W) g) ∂μ := by
    intro x hx s
    rw [integral_congr_ae (Filter.Eventually.of_forall (hTJ x hx s))]
    exact integral_mul_left_eq_self (μ := μ) (fun y : GL (Fin n) F =>
      Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F)) *
        detPow y s * ℓx x ((φ : GL (Fin n) F → W) y)) x

  obtain ⟨r, A, -, hA⟩ := hΦ.exists_invariant
  set h : ℤ → GL (Fin n) F → ℂ := fun k =>
    {g : GL (Fin n) F | ordDet g = k}.indicator fun g => Φ (g : Matrix (Fin n) (Fin n) F)
    with hhdef
  have hhcs : ∀ k, HasCompactSupport (h k) := fun k =>
    HasCompactSupport.intro (isCompact_shell F n A k) fun g hg => by
      simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hk
      · by_contra hne
        exact hg ⟨hA _ hne, hk⟩
      · rfl
  have hhl : ∀ k, ∀ k' ∈ K, ∀ g, h k (k' * g) = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), zero_add, Units.val_mul, (hΦK k' hk' _).1]
  have hhr : ∀ k, ∀ k' ∈ K, ∀ g, h k (g * k') = h k g := fun k k' hk' g => by
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq, ordDet_mul,
      ordDet_of_mem_integralGL (hK0 k' hk'), add_zero, Units.val_mul, (hΦK k' hk' _).2]

  have hcont : ∀ H : GL (Fin n) F → ℂ, (∀ g, ∀ k ∈ K, H (g * k) = H g) → Continuous H :=
    fun H hH => (isLocallyConstant_of_mul_right hKo hH).continuous
  have hfr : ∀ g, ∀ k ∈ K, lam (parabolicInd F n β σ (g * k) φ) = lam (parabolicInd F n β σ g φ) :=
    fun g k hk => by rw [map_mul, Module.End.mul_apply, show parabolicInd F n β σ k φ = φ from hφK k hk]
  have hφr : ∀ x g, ∀ k ∈ K, (φ : GL (Fin n) F → W) (x * (g * k)) = (φ : GL (Fin n) F → W) (x * g) :=
    fun x g k hk => by
      have := congrArg (fun ψ : parabolicIndSpace F n β σ => (ψ : GL (Fin n) F → W) (x * g)) (hφK k hk)
      simp only [coe_indRep_apply] at this
      rw [← mul_assoc, this]
  have hdetr : ∀ s g, ∀ k ∈ K, detPow (g * k) s = detPow g s := fun s g k hk => by
    rw [detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]
  have hΦr : ∀ g, ∀ k ∈ K, Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Φ (g : Matrix (Fin n) (Fin n) F) := fun g k hk => by rw [Units.val_mul, (hΦK k hk _).2]

  have hhf : ∀ k, Integrable (fun g => ‖h k g * lam (parabolicInd F n β σ g φ)‖) μ := fun k =>
    ((hcont _ fun g k' hk' => by rw [hhr k k' hk', hfr g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).mul_right.norm
  have hhint : ∀ k, ∀ x ∈ R, Integrable (fun g => ‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) μ :=
    fun k x _ => ((hcont _ fun g k' hk' => by rw [hhr k k' hk']).norm.mul
      (hcont _ fun g k' hk' => by rw [hφr x g k' hk']).norm).integrable_of_hasCompactSupport
      (hhcs k).norm.mul_right
  have hshellZ : ∀ s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) g =
      qs F s ^ k * (h k g * lam (parabolicInd F n β σ g φ)) := by
    intro s k g
    simp only [h, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [hf g, detPow_eq_qs_zpow, hk]; ring
    · simp
  have hshellT : ∀ x s k g, {g : GL (Fin n) F | ordDet g = k}.indicator (T x s) g =
      qs F s ^ k * (h k g * ℓx x ((φ : GL (Fin n) F → W) (x * g))) := by
    intro x s k g
    simp only [h, T, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hk
    · rw [detPow_eq_qs_zpow, hk]; ring
    · simp

  have hZint : ∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s) μ := by
    intro s hs
    refine ⟨(hcont _ fun g k hk => by
      rw [hΦr g k hk, hdetr s g k hk, hf, hf, hfr g k hk]).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [← ofReal_norm]
    rw [lintegral_eq_tsum_shell]
    have hterm : ∀ k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
        ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ ≤
        ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal ‖T x s g‖ ∂μ := by
      intro k
      have e1 : ∀ g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖) g =
          ENNReal.ofReal (‖qs F s‖ ^ k) * ENNReal.ofReal ‖h k g * lam (parabolicInd F n β σ g φ)‖ := by
        intro g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← hshellZ s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      have e2 : ∀ x g, {g : GL (Fin n) F | ordDet g = k}.indicator (fun g => ENNReal.ofReal
          ‖T x s g‖) g = ENNReal.ofReal (‖qs F s‖ ^ k) *
            ENNReal.ofReal (‖h k g‖ * ‖ℓx x ((φ : GL (Fin n) F → W) (x * g))‖) := by
        intro x g
        rw [← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← norm_zpow, ← norm_mul,
          ← norm_mul, ← hshellT x s k g]
        by_cases hg : g ∈ {g : GL (Fin n) F | ordDet g = k}
        · simp [Set.indicator_of_mem hg]
        · simp [Set.indicator_of_notMem hg]
      rw [← lintegral_indicator (measurableSet_shell k), lintegral_congr e1,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp_rw [← lintegral_indicator (measurableSet_shell k), e2]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← Finset.mul_sum]
      exact mul_le_mul' le_rfl (lintegral_norm_mul_coeff_le μ hKc hKo hlamK hφK hdec (hhcs k)
        (hhl k) (hhr k) (hhf k) (hhint k))
    calc ∑' k : ℤ, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k}, ENNReal.ofReal
          ‖Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s‖ ∂μ
        ≤ ∑' k : ℤ, ∑ x ∈ R, ∫⁻ g in {g : GL (Fin n) F | ordDet g = k},
            ENNReal.ofReal ‖T x s g‖ ∂μ := ENNReal.tsum_le_tsum hterm
      _ = ∑ x ∈ R, ∫⁻ g, ENNReal.ofReal ‖T x s g‖ ∂μ := by
          rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          exact Finset.sum_congr rfl fun x _ => (lintegral_eq_tsum_shell μ _).symm
      _ < ∞ := by
          refine ENNReal.sum_lt_top.2 fun x hx => ?_
          have := (hTint x hx s hs).2
          simpa [HasFiniteIntegral, ofReal_norm] using this
  refine ⟨hZint, ?_⟩

  refine ⟨∑ x ∈ R, N x, ∑ x ∈ R, P x * X ^ (∑ y ∈ R, N y - N x), fun s hs => ?_⟩
  have hZsum := hasSum_integral_shell μ (hZint s hs)
  have hTsum : ∀ x ∈ R, HasSum (fun k : ℤ => ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ)
      (∫ g, T x s g ∂μ) := fun x hx => hasSum_integral_shell μ (hTint x hx s hs)
  have hsum := hasSum_sum hTsum
  have hshell_eq : ∀ k : ℤ, ∫ g in {g : GL (Fin n) F | ordDet g = k},
      Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g in {g : GL (Fin n) F | ordDet g = k}, T x s g ∂μ := by
    intro k
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellZ s k]
    rw [integral_const_mul, integral_mul_coeff_eq μ hKc hKo hφK hdec (hhcs k) (hhl k) (hhr k),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← integral_indicator (measurableSet_shell k)]
    simp_rw [hshellT x s k]
    rw [integral_const_mul]
  have hZ : ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g * detPow g s ∂μ =
      ∑ x ∈ R, ∫ g, T x s g ∂μ := by
    refine hZsum.unique ?_
    convert hsum using 1
    funext k
    exact hshell_eq k
  have hterm : ∀ x ∈ R, D.eval (qs F s) * ∫ g, T x s g ∂μ = (P x).eval (qs F s) / qs F s ^ N x := by
    intro x hx
    rw [hTeq x hx s]
    exact hJeq x s hs
  rw [hZ, Finset.mul_sum, Finset.sum_congr rfl hterm, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hle : N x ≤ ∑ y ∈ R, N y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
  rw [eval_mul, eval_pow, eval_X, pow_sub₀ _ (qs_ne_zero s) hle]
  field_simp
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (qs_ne_zero s))).symm

end Core

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Polynomial

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

section RatFunc

theorem exists_eval_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → Q.eval x ≠ 0 := by
  classical
  set S : Finset ℝ := ((Q.roots.toFinset).filter (· ≠ 0)).image (‖·‖)
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_, fun x hx hxε hQx => ?_⟩
    · obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.1 (S.min'_mem hS)
      rw [← hyeq]
      exact norm_pos_iff.2 (Finset.mem_filter.1 hy).2
    · have hmem : ‖x‖ ∈ S := Finset.mem_image.2 ⟨x, Finset.mem_filter.2
        ⟨Multiset.mem_toFinset.2 ((mem_roots hQ).2 hQx), hx⟩, rfl⟩
      exact absurd (S.min'_le _ hmem) (not_le.2 hxε)
  · refine ⟨1, one_pos, fun x hx _ hQx => hS ⟨‖x‖, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
      ⟨Multiset.mem_toFinset.2 ((mem_roots hQ).2 hQx), hx⟩, rfl⟩⟩⟩

theorem exists_eval_denom_ne_zero (R : RatFunc ℂ) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R.denom.eval x ≠ 0 :=
  exists_eval_ne_zero R.denom_ne_zero

theorem exists_eval_mul (R₁ R₂ : RatFunc ℂ) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
      (R₁ * R₂).eval (RingHom.id ℂ) x = R₁.eval (RingHom.id ℂ) x * R₂.eval (RingHom.id ℂ) x := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_eval_denom_ne_zero R₁
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_eval_denom_ne_zero R₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx hxε => ?_⟩
  exact RatFunc.eval_mul (f := RingHom.id ℂ) (a := x) (h₁ x hx (hxε.trans_le (min_le_left _ _)))
    (h₂ x hx (hxε.trans_le (min_le_right _ _)))

end RatFunc

theorem qs_add (a b : ℂ) : qs F (a + b) = qs F a * qs F b := by
  rw [qs, qs, qs, neg_add, Complex.cpow_add _ _
    (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero)]

theorem exists_qs_of_small (S : ℝ) : ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
    ∃ s : ℂ, S < s.re ∧ qs F s = x := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by
    exact_mod_cast LocalField.one_lt_residueCard (K := F)
  refine ⟨(LocalField.residueCard F : ℝ) ^ (-S), Real.rpow_pos_of_pos (by linarith) _,
    fun x hx hxε => ?_⟩
  obtain ⟨s, hs, hre⟩ := exists_qs_eq (F := F) hx
  refine ⟨s, ?_, hs⟩
  rw [hre]
  have h1 : Real.logb (LocalField.residueCard F) ‖x‖ <
      Real.logb (LocalField.residueCard F) ((LocalField.residueCard F : ℝ) ^ (-S)) :=
    Real.logb_lt_logb hq (norm_pos_iff.2 hx) hxε
  rw [Real.logb_rpow (by linarith) hq.ne'] at h1
  linarith

def zetaIntegral (μ : Measure (GL (Fin n) F)) (Φ : Matrix (Fin n) (Fin n) F → ℂ)
    (f : GL (Fin n) F → ℂ) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * f g * detPow g (s + ((n : ℂ) - 1) / 2) ∂μ

def zetaSet (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) :
    Set (RatFunc ℂ) :=
  {R | ∃ (Φ : Matrix (Fin n) (Fin n) F → ℂ) (v : V) (ℓ : Module.Dual ℂ V),
    IsSchwartzBruhat Φ ∧ ℓ ∈ smoothVectors (Representation.dual π) ∧
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        zetaIntegral μ Φ (matrixCoeff π v ℓ) s = R.eval (RingHom.id ℂ) (qs F s)}

def zetaIdeal (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) :
    Submodule ℂ (RatFunc ℂ) :=
  Submodule.span ℂ (zetaSet π μ)

variable {π : Representation ℂ (GL (Fin n) F) V}

theorem re_shift (s : ℂ) : (s + ((n : ℂ) - 1) / 2).re = s.re + ((n : ℝ) - 1) / 2 := by
  simp [Complex.add_re, Complex.sub_re]

theorem exists_zeta_rat [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ (∀ s : ℂ, s₀ < s.re → D.eval (qs F s) ≠ 0) ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g (s + ((n : ℂ) - 1) / 2)) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          zetaIntegral μ Φ (matrixCoeff π v ℓ) s =
            (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D)).eval
              (RingHom.id ℂ) (qs F s) := by
  obtain ⟨s₀, D, hD0, hcore⟩ := exists_zeta_core hπ μ
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  set D' : ℂ[X] := D.comp (C c * X) with hD'def
  have hD'0 : D'.eval 0 = 1 := by simp [D', hD0]
  have hD'ne : D' ≠ 0 := fun h => by rw [h, eval_zero] at hD'0; exact zero_ne_one hD'0
  obtain ⟨ε, hε, hεD⟩ := exists_eval_ne_zero hD'ne
  obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
  have hre : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re →
      s₀ < (s + ((n : ℂ) - 1) / 2).re := fun s hs => by
    have := (le_max_left _ _).trans_lt hs
    rw [re_shift]
    linarith
  have hDs : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re → D'.eval (qs F s) ≠ 0 :=
    fun s hs => hεD _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs))
  refine ⟨max (s₀ - ((n : ℝ) - 1) / 2) s₁, D', hD'0, hDs, fun Φ hΦ v ℓ hℓ => ?_⟩
  obtain ⟨hint, N, P, hP⟩ := hcore Φ hΦ v ℓ hℓ
  refine ⟨fun s hs => hint _ (hre s hs), N, C (c ^ N)⁻¹ * P.comp (C c * X), fun s hs => ?_⟩
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hDx := hDs s hs
  have hQ : (X ^ N * D').eval (qs F s) ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X]
    exact mul_ne_zero (pow_ne_zero _ hx) hDx
  rw [eval_div_algebraMap _ _ hQ]
  have h1 := hP _ (hre s hs)
  rw [qs_add, ← hcdef] at h1
  have hDx' : D.eval (qs F s * c) ≠ 0 := by
    rw [mul_comm]
    rw [hD'def, eval_comp, eval_mul, eval_C, eval_X] at hDx
    exact hDx
  have h2 := eq_div_of_mul_eq hDx' ((mul_comm _ _).trans h1)
  rw [zetaIntegral, h2]
  simp only [D', eval_mul, eval_comp, eval_C, eval_X, eval_pow]
  rw [mul_comm c (qs F s), mul_pow]
  field_simp

theorem exists_integrable_zetaIntegral [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
      ℓ ∈ smoothVectors (Representation.dual π) → ∀ s : ℂ, s₀ < s.re →
        Integrable (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
          detPow g (s + ((n : ℂ) - 1) / 2)) μ := by
  obtain ⟨s₀, _, _, _, h⟩ := exists_zeta_rat hπ μ
  exact ⟨s₀, fun Φ hΦ v ℓ hℓ => (h Φ hΦ v ℓ hℓ).1⟩


theorem zetaIntegral_translate (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a : GL (Fin n) F)
    (Φ : Matrix (Fin n) (Fin n) F → ℂ) (v : V) (ℓ : Module.Dual ℂ V) (s : ℂ) :
    zetaIntegral μ (fun Y => Φ (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Y))
      (matrixCoeff π v (Representation.dual π a ℓ)) s =
      detPow a (s + ((n : ℂ) - 1) / 2) * zetaIntegral μ Φ (matrixCoeff π v ℓ) s := by
  rw [zetaIntegral, zetaIntegral, ← integral_const_mul,
    ← integral_mul_left_eq_self (μ := μ) _ a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [matrixCoeff, dual_apply_apply, ← Module.End.mul_apply, ← map_mul, ← mul_assoc,
    ← Units.val_mul, inv_mul_cancel, one_mul, detPow_mul]
  ring

theorem mem_zetaSet_of_translate (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {R R' : RatFunc ℂ}
    (hR : R ∈ zetaSet π μ) (a : GL (Fin n) F)
    (hR' : ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → R'.eval (RingHom.id ℂ) (qs F s) =
      detPow a (s + ((n : ℂ) - 1) / 2) * R.eval (RingHom.id ℂ) (qs F s)) :
    R' ∈ zetaSet π μ := by
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  obtain ⟨s₁, hs₁⟩ := hR'
  refine ⟨fun Y => Φ (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Y), v,
    Representation.dual π a ℓ, hΦ.comp_mul_left a⁻¹, smooth_apply_mem _ hℓ a, max s₀ s₁,
    fun s hs => ?_⟩
  rw [zetaIntegral_translate, hZ s ((le_max_left _ _).trans_lt hs),
    hs₁ s ((le_max_right _ _).trans_lt hs)]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem ordDet_diagPow_single [NeZero n] :
    ordDet (Cartan.diagPow F n (Pi.single 0 1)) = 1 := by
  rw [ordDet, Cartan.coe_diagPow, det_diagonal, Finset.prod_eq_single (0 : Fin n)]
  · simp [LocalField.ord_uniformizer (irreducible_uniformizer F)]
  · intro b _ hb
    simp [hb]
  · simp

theorem X_mul_mem_zetaIdeal [NeZero n] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {R : RatFunc ℂ} (hR : R ∈ zetaIdeal π μ) : RatFunc.X * R ∈ zetaIdeal π μ := by
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  refine Submodule.span_induction (p := fun R _ => RatFunc.X * R ∈ zetaIdeal π μ) ?_ ?_ ?_ ?_ hR
  · intro R hR
    set a := Cartan.diagPow F n (Pi.single 0 1)
    have hmem : RatFunc.C c * RatFunc.X * R ∈ zetaSet π μ := by
      refine mem_zetaSet_of_translate μ hR a ?_
      obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C c * RatFunc.X) R
      obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
      refine ⟨s₁, fun s hs => ?_⟩
      rw [hεR _ (qs_ne_zero s) (hs₁ s hs), detPow_eq_qs_zpow, ordDet_diagPow_single, zpow_one,
        qs_add, ← hcdef, RatFunc.eval_mul (f := RingHom.id ℂ) (a := qs F s) (by simp) (by simp),
        RatFunc.eval_C, RatFunc.eval_X]
      simp only [RingHom.id_apply]
      ring
    have : RatFunc.X * R = c⁻¹ • (RatFunc.C c * RatFunc.X * R) := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c' x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem X_inv_mul_mem_zetaIdeal [NeZero n] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {R : RatFunc ℂ} (hR : R ∈ zetaIdeal π μ) : RatFunc.X⁻¹ * R ∈ zetaIdeal π μ := by
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  refine Submodule.span_induction (p := fun R _ => RatFunc.X⁻¹ * R ∈ zetaIdeal π μ) ?_ ?_ ?_ ?_ hR
  · intro R hR
    set a := Cartan.diagPow F n (Pi.single 0 1)
    have hXinv : ∀ x : ℂ, x ≠ 0 → (RatFunc.X⁻¹ : RatFunc ℂ).eval (RingHom.id ℂ) x = x⁻¹ := by
      intro x hx
      have := eval_div_algebraMap 1 X (x := x) (by simpa using hx)
      rw [map_one, RatFunc.algebraMap_X, one_div] at this
      rw [this]
      simp
    have hmem : RatFunc.C c⁻¹ * RatFunc.X⁻¹ * R ∈ zetaSet π μ := by
      refine mem_zetaSet_of_translate μ hR a⁻¹ ?_
      obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C c⁻¹ * RatFunc.X⁻¹) R
      obtain ⟨ε', hε', hεR'⟩ := exists_eval_mul (RatFunc.C c⁻¹) (RatFunc.X⁻¹ : RatFunc ℂ)
      obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) (lt_min hε hε')
      refine ⟨s₁, fun s hs => ?_⟩
      have hsm := hs₁ s hs
      have hinv : ordDet a⁻¹ = -1 := by
        have h1 := ordDet_mul a⁻¹ a
        rw [inv_mul_cancel, ordDet_diagPow_single] at h1
        have h0 : ordDet (1 : GL (Fin n) F) = 0 := by simp [ordDet, LocalField.ord_one]
        omega
      rw [hεR _ (qs_ne_zero s) (hsm.trans_le (min_le_left _ _)),
        hεR' _ (qs_ne_zero s) (hsm.trans_le (min_le_right _ _)), RatFunc.eval_C,
        hXinv _ (qs_ne_zero s), detPow_eq_qs_zpow, hinv, qs_add, ← hcdef]
      simp only [RingHom.id_apply, _root_.zpow_neg, zpow_one, mul_inv]
      ring
    have : RatFunc.X⁻¹ * R = c • (RatFunc.C c⁻¹ * RatFunc.X⁻¹ * R) := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c' x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem exists_zetaSet_eq [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧ ∀ R ∈ zetaSet π μ, ∃ (N : ℕ) (P : ℂ[X]),
      R = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D) := by
  obtain ⟨s₀, D, hD0, -, h⟩ := exists_zeta_rat hπ μ
  refine ⟨D, hD0, fun R hR => ?_⟩
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₁, hZ⟩ := hR
  obtain ⟨-, N, P, hP⟩ := h Φ hΦ v ℓ hℓ
  refine ⟨N, P, ?_⟩
  obtain ⟨ε, hε, hεs⟩ := exists_qs_of_small (F := F) (max s₀ s₁)
  refine eq_of_eval_eq hε fun x hx hxε => ?_
  obtain ⟨s, hs, rfl⟩ := hεs x hx hxε
  rw [← hZ s ((le_max_right _ _).trans_lt hs), hP s ((le_max_left _ _).trans_lt hs)]

theorem exists_denominator_zetaIdeal [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ R ∈ zetaIdeal π μ, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra := by
  obtain ⟨D, hD0, hD⟩ := exists_zetaSet_eq hπ μ
  have hDne : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h
    rw [h, eval_zero] at hD0
    exact zero_ne_one hD0
  refine ⟨D, hD0, fun R hR => ?_⟩
  refine Submodule.span_induction
    (p := fun R _ => algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) ?_ ?_ ?_ ?_ hR
  · intro R hR
    obtain ⟨N, P, rfl⟩ := hD R hR
    refine mem_laurentSubalgebra_iff.2 ⟨P, N, ?_⟩
    rw [map_mul, map_pow, RatFunc.algebraMap_X]
    have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    field_simp
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Subalgebra.smul_mem _ hx c

theorem one_mem_zetaIdeal (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (hπ : IsSmooth π)
    [Nontrivial V] : (1 : RatFunc ℂ) ∈ zetaIdeal π μ := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ v).mem_nhds (one_mem (stabilizerOf π v)))
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hvK : v ∈ fixedVectors π K := fun k hk => hm hk

  obtain ⟨f0, hf0⟩ : ∃ f0 : Module.Dual ℂ (fixedVectors π K), f0 ⟨v, hvK⟩ = 1 := by
    have hne : (⟨v, hvK⟩ : fixedVectors π K) ≠ 0 := fun h => hv (congrArg Subtype.val h)
    have hnot : ¬ ∀ g : Module.Dual ℂ (fixedVectors π K), g ⟨v, hvK⟩ = 0 := fun h =>
      hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    obtain ⟨g, hg⟩ := not_forall.1 hnot
    exact ⟨(g ⟨v, hvK⟩)⁻¹ • g, by simp [hg]⟩
  set ℓ : Module.Dual ℂ V := f0 ∘ₗ fixedProj π hπ hKc hKo with hℓdef
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := fun k hk x => by
    simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, fixedProj_apply_act hπ hKc hKo hk]
  have hℓ : ℓ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hℓK)
  have hℓv : ℓ v = 1 := by
    have : fixedProj π hπ hKc hKo v = ⟨v, hvK⟩ := Subtype.ext (fixedProj_apply_of_mem hπ hKc hKo hvK)
    simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, this, hf0]

  set S : Set (Matrix (Fin n) (Fin n) F) := Units.val '' (K : Set (GL (Fin n) F)) with hSdef
  have hSo : IsOpen S := (Measures.isOpenEmbedding_val F n).isOpenMap _ hKo
  have hSc : IsCompact S := hKc.image Units.continuous_val
  set Φ : Matrix (Fin n) (Fin n) F → ℂ := S.indicator 1 with hΦdef
  have hΦ : IsSchwartzBruhat Φ := by
    refine ⟨?_, HasCompactSupport.intro hSc fun X hX => Set.indicator_of_notMem hX _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro X
    by_cases hX : X ∈ S
    · exact ⟨S, hSo, hX, fun Y hY => by simp [Φ, Set.indicator_of_mem hY, Set.indicator_of_mem hX]⟩
    · exact ⟨Sᶜ, hSc.isClosed.isOpen_compl, hX, fun Y hY => by
        simp [Φ, Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  have hΦg : ∀ g : GL (Fin n) F, Φ (g : Matrix (Fin n) (Fin n) F) =
      (K : Set (GL (Fin n) F)).indicator 1 g := fun g => by
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem hg, hΦdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hg)]
      rfl
    · rw [Set.indicator_of_notMem hg, hΦdef, Set.indicator_of_notMem]
      rintro ⟨g', hg', hgg'⟩
      exact hg (Units.val_injective hgg' ▸ hg')

  have hZ : ∀ s, zetaIntegral μ Φ (matrixCoeff π v ℓ) s = (μ.real (K : Set (GL (Fin n) F)) : ℂ) := by
    intro s
    rw [zetaIntegral]
    have hfun : (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)) = (K : Set (GL (Fin n) F)).indicator fun _ => (1 : ℂ) := by
      funext g
      rw [hΦg g]
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, matrixCoeff, hvK g hg, hℓv,
          detPow_of_mem_integralGL (congruenceSubgroup_le F n m hg)]
        simp
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
        simp
    rw [hfun, integral_indicator_const _ hKo.measurableSet]
    simp
  have hmem : RatFunc.C (μ.real (K : Set (GL (Fin n) F)) : ℂ) ∈ zetaSet π μ :=
    ⟨Φ, v, ℓ, hΦ, hℓ, 0, fun s _ => by rw [hZ, RatFunc.eval_C]; rfl⟩
  have hpos : (μ.real (K : Set (GL (Fin n) F)) : ℂ) ≠ 0 := by
    have : 0 < μ.real (K : Set (GL (Fin n) F)) :=
      ENNReal.toReal_pos (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩) hKc.measure_lt_top.ne
    exact_mod_cast this.ne'
  have h1 : (1 : RatFunc ℂ) = ((μ.real (K : Set (GL (Fin n) F)) : ℂ))⁻¹ •
      RatFunc.C (μ.real (K : Set (GL (Fin n) F)) : ℂ) := by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← map_mul, inv_mul_cancel₀ hpos, map_one]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem existsUnique_zetaIdeal_eq [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃! P : ℂ[X], P.eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ zetaIdeal π μ ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V := ⟨⟨v, 0, hv⟩⟩
  obtain ⟨D, hD0, hD⟩ := exists_denominator_zetaIdeal hπ μ
  refine existsUnique_eq_laurent_div _ (fun R hR => X_mul_mem_zetaIdeal μ hR)
    (fun R hR => X_inv_mul_mem_zetaIdeal μ hR) (one_mem_zetaIdeal μ hπ.1) ⟨D, ?_, hD⟩
  intro h
  rw [h, eval_zero] at hD0
  exact zero_ne_one hD0

omit [BorelSpace (GL (Fin n) F)] in
theorem zetaIdeal_le_smul (μ : Measure (GL (Fin n) F)) {c : NNReal} (hc : c ≠ 0) :
    zetaIdeal π μ ≤ zetaIdeal π (c • μ) := by
  refine Submodule.span_le.2 fun R hR => ?_
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hmem : RatFunc.C ((c : ℝ) : ℂ) * R ∈ zetaSet π (c • μ) := by
    obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C ((c : ℝ) : ℂ)) R
    obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
    refine ⟨Φ, v, ℓ, hΦ, hℓ, max s₀ s₁, fun s hs => ?_⟩
    rw [hεR _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs)), RatFunc.eval_C,
      ← hZ s ((le_max_left _ _).trans_lt hs), zetaIntegral, zetaIntegral,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    rfl
  have h : R = ((c : ℝ) : ℂ)⁻¹ • (RatFunc.C ((c : ℝ) : ℂ) * R) := by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc',
      map_one, one_mul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem zetaIdeal_eq_of_isHaarMeasure (μ ν : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] : zetaIdeal π μ = zetaIdeal π ν := by
  have key : ∀ (μ ν : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] [ν.IsHaarMeasure],
      zetaIdeal π μ ≤ zetaIdeal π ν := by
    intro μ ν _ _
    rw [Measure.isMulLeftInvariant_eq_smul ν μ]
    exact zetaIdeal_le_smul μ (Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ).ne'
  exact le_antisymm (key μ ν) (key ν μ)

variable (π) in

def LPolynomial : ℂ[X] := by
  classical
  exact if h : ∃ P : ℂ[X], P.eval 0 = 1 ∧ ∀ R : RatFunc ℂ,
      R ∈ zetaIdeal π (Measure.haar : Measure (GL (Fin n) F)) ↔
        ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P then h.choose else 1

variable (π) in

def LFunction (s : ℂ) : ℂ :=
  ((LPolynomial π).eval (qs F s))⁻¹

theorem LPolynomial_spec [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    (LPolynomial π).eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ zetaIdeal π μ ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π) := by
  classical
  have h := (existsUnique_zetaIdeal_eq hπ (Measure.haar : Measure (GL (Fin n) F))).exists
  rw [LPolynomial, dif_pos h]
  obtain ⟨h0, hiff⟩ := h.choose_spec
  refine ⟨h0, fun R => ?_⟩
  rw [zetaIdeal_eq_of_isHaarMeasure μ Measure.haar]
  exact hiff R

end GodementJacquet

end GroundTheory.Automorphic
end
end
