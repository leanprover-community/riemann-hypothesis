import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalFibPowExplicit
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegral

section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.CovTest.SwapLine

def linearSum (a b : ℤ) : MvPolynomial (Fin 2) ℝ := C ((a : ℝ) + b) * X 0 + C 2 * X 1

def quadraticPart (a b : ℤ) : MvPolynomial (Fin 2) ℝ := C ((a : ℝ) * b) * X 0 ^ 2 + C ((a : ℝ) + b) * (X 0 * X 1) + X 1 ^ 2

noncomputable def swapPow (a b : ℤ) : ℕ → Polynomial (MvPolynomial (Fin 2) ℝ)
  | 0 => Polynomial.C (C 2)
  | 1 => Polynomial.C (linearSum a b)
  | n + 2 => Polynomial.C (linearSum a b) * swapPow a b (n + 1) -
      (Polynomial.C (quadraticPart a b) + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * swapPow a b n

def swapR (d : ℕ) (a b : ℤ) (i : ℕ) : MvPolynomial (Fin 2) ℝ := (swapPow a b (d + 2)).coeff i

private theorem hom_cast {σ : Type} {φ : MvPolynomial σ ℝ} {m k : ℕ} (h : φ.IsHomogeneous m) (e : m = k) :
    φ.IsHomogeneous k := e ▸ h

private theorem hom_mul_of {σ : Type} {p f : MvPolynomial σ ℝ} {k m N : ℕ} (hp : p.IsHomogeneous k)
    (hf : f.IsHomogeneous m) (hz : k + m ≠ N → f = 0) : (p * f).IsHomogeneous N := by
  by_cases h : k + m = N
  · exact h ▸ hp.mul hf
  · rw [hz h, mul_zero]; exact isHomogeneous_zero _ _ _

theorem linearSum_isHomogeneous (a b : ℤ) : (linearSum a b).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)

theorem quadraticPart_isHomogeneous (a b : ℤ) : (quadraticPart a b).IsHomogeneous 2 := by
  have h0 := isHomogeneous_X ℝ (0 : Fin 2)
  have h1 := isHomogeneous_X ℝ (1 : Fin 2)
  refine ((hom_cast ((isHomogeneous_C (Fin 2) _).mul (h0.pow 2)) (by omega)).add
    (hom_cast ((isHomogeneous_C (Fin 2) _).mul (h0.mul h1)) (by omega))).add (hom_cast (h1.pow 2) (by omega))

theorem swapPow_coeff_add_two (a b : ℤ) (n i : ℕ) : (swapPow a b (n + 2)).coeff (i + 1) =
    linearSum a b * (swapPow a b (n + 1)).coeff (i + 1) - (quadraticPart a b * (swapPow a b n).coeff (i + 1) +
      C (((a : ℝ) - b) ^ 2) * (swapPow a b n).coeff i) := by
  rw [swapPow, show ∀ T : Polynomial (MvPolynomial (Fin 2) ℝ), (Polynomial.C (quadraticPart a b) +
      Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * T =
      Polynomial.C (quadraticPart a b) * T + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * (Polynomial.X * T) from fun T => by ring]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

theorem swapPow_coeff_zero_add_two (a b : ℤ) (n : ℕ) : (swapPow a b (n + 2)).coeff 0 =
    linearSum a b * (swapPow a b (n + 1)).coeff 0 - quadraticPart a b * (swapPow a b n).coeff 0 := by
  rw [swapPow, show ∀ T : Polynomial (MvPolynomial (Fin 2) ℝ), (Polynomial.C (quadraticPart a b) +
      Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * T =
      Polynomial.C (quadraticPart a b) * T + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * (Polynomial.X * T) from fun T => by ring]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero, mul_zero,
    add_zero]

theorem swapPow_coeff (a b : ℤ) (n : ℕ) : ∀ i, ((swapPow a b n).coeff i).IsHomogeneous (n - 2 * i) ∧
    (n < 2 * i → (swapPow a b n).coeff i = 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · intro i
    rcases i with _ | i
    · simp only [swapPow, Polynomial.coeff_C_zero]
      exact ⟨isHomogeneous_C _ _, fun h => absurd h (by omega)⟩
    · simp only [swapPow, Polynomial.coeff_C_succ]
      exact ⟨isHomogeneous_zero _ _ _, by simp⟩
  · intro i
    rcases i with _ | i
    · simp only [swapPow, Polynomial.coeff_C_zero]
      exact ⟨linearSum_isHomogeneous a b, fun h => absurd h (by omega)⟩
    · simp only [swapPow, Polynomial.coeff_C_succ]
      exact ⟨isHomogeneous_zero _ _ _, by simp⟩
  · have h1 := ih (n + 1) (by omega)
    have h0 := ih n (by omega)
    intro i
    rcases i with _ | i
    · rw [swapPow_coeff_zero_add_two]
      refine ⟨(hom_mul_of (linearSum_isHomogeneous a b) (h1 0).1 fun h => absurd h (by omega)).sub
        (hom_mul_of (quadraticPart_isHomogeneous a b) (h0 0).1 fun h => absurd h (by omega)), fun h => absurd h (by omega)⟩
    · rw [swapPow_coeff_add_two]
      refine ⟨(hom_mul_of (linearSum_isHomogeneous a b) (h1 (i + 1)).1 fun h => (h1 (i + 1)).2 (by omega)).sub
        ((hom_mul_of (quadraticPart_isHomogeneous a b) (h0 (i + 1)).1 fun h => (h0 (i + 1)).2 (by omega)).add
          (hom_mul_of (isHomogeneous_C (Fin 2) _) (h0 i).1 fun h => absurd h (by omega))), fun h => ?_⟩
      rw [(h1 (i + 1)).2 (by omega), (h0 (i + 1)).2 (by omega), (h0 i).2 (by omega)]
      simp

theorem swapPow_natDegree_lt (a b : ℤ) (n : ℕ) : (swapPow a b n).natDegree < n + 1 := by
  refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_)
  exact (swapPow_coeff a b n N).2 (by omega)

theorem swapR_isHomogeneous (d : ℕ) (a b : ℤ) (i : ℕ) : (swapR d a b i).IsHomogeneous (d + 2 - 2 * i) :=
  (swapPow_coeff a b (d + 2) i).1

theorem swapR_eq_zero (d : ℕ) (a b : ℤ) {i : ℕ} (h : d + 2 < 2 * i) : swapR d a b i = 0 :=
  (swapPow_coeff a b (d + 2) i).2 h

theorem eval_swapPow {S : Type*} [CommRing S] [Algebra ℝ S] (a b : ℤ) (x : Fin 3 → S) (n : ℕ) :
    Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b n) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ n +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ n := by
  have hs : (aeval ![x 0 + x 1, x 2]).toRingHom (linearSum a b) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) + (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) := by
    simp only [linearSum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, aeval_C, aeval_X, map_ofNat,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have hp : (aeval ![x 0 + x 1, x 2]).toRingHom (quadraticPart a b) +
      (aeval ![x 0 + x 1, x 2]).toRingHom (C (((a : ℝ) - b) ^ 2)) * (x 0 * x 1) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) * (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) := by
    simp only [quadraticPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow, map_sub, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have key : ∀ n, Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b n) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ n +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ n ∧
      Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b (n + 1)) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ (n + 1) +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [swapPow, Polynomial.eval₂_C]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, map_ofNat]
        ring
      · simp only [swapPow, Polynomial.eval₂_C]
        rw [hs]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [swapPow]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_C,
        Polynomial.eval₂_X, ih.1, ih.2]
      rw [hs, hp]
      ring
  exact (key n).1

theorem aeval_swapSum {S : Type*} [CommRing S] [Algebra ℝ S] (d : ℕ) (a b : ℤ) (x : Fin 3 → S) :
    aeval x (swapSum d a b) =
      ∑ i ∈ Finset.range (d + 3), (x 0 * x 1) ^ i * aeval ![x 0 + x 1, x 2] (swapR d a b i) := by
  have h1 := eval_swapPow a b x (d + 2)
  rw [Polynomial.eval₂_eq_sum_range' _ (swapPow_natDegree_lt a b (d + 2))] at h1
  have h2 : aeval x (swapSum d a b) = (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ (d + 2) +
      (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ (d + 2) := by
    simp only [swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul]
  rw [h2, ← h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


def swapP (d : ℕ) (a b : ℤ) : MvPolynomial (Fin 5) ℝ :=
  ∑ i ∈ Finset.range (d + 3), (∑ k ∈ Finset.range i, (X 3 * X 4) ^ k * (X 0 * (X 3 + X 4 - X 0)) ^ (i - 1 - k)) *
    aeval ![X 3 + X 4, X 2] (swapR d a b i)

theorem onLine_sub_onBase_eq (d : ℕ) (a b : ℤ) :
    onLine d a b - onBase d a b = -((X 4 - X 0) * (X 3 - X 0)) * swapP d a b := by
  have e1 : (X 0 + (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) = X 3 + X 4 := by ring
  have e2 : (X 4 * X 3 : MvPolynomial (Fin 5) ℝ) = X 3 * X 4 := mul_comm _ _
  have e3 : (X 4 + X 3 : MvPolynomial (Fin 5) ℝ) = X 3 + X 4 := add_comm _ _
  rw [onLine, onBase, aeval_swapSum, aeval_swapSum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e1, e2,
    e3]
  rw [swapP, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := geom_sum₂_mul (X 3 * X 4 : MvPolynomial (Fin 5) ℝ) (X 0 * (X 3 + X 4 - X 0)) i
  linear_combination (aeval ![X 3 + X 4, X 2] (swapR d a b i)) * h

private theorem swapR_aeval_isHomogeneous_five_vars (d : ℕ) (a b : ℤ) (i : ℕ) :
    (aeval ![X 3 + X 4, X 2] (swapR d a b i) : MvPolynomial (Fin 5) ℝ).IsHomogeneous (1 * (d + 2 - 2 * i)) :=
  (swapR_isHomogeneous d a b i).aeval _ (Fin.forall_fin_two.2 ⟨(isHomogeneous_X ℝ 3).add (isHomogeneous_X ℝ 4),
    isHomogeneous_X ℝ 2⟩)

theorem swapP_isHomogeneous (d : ℕ) (a b : ℤ) : (swapP d a b).IsHomogeneous d := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  rcases i with _ | i
  · simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
    exact isHomogeneous_zero _ _ _
  · refine hom_mul_of (k := 2 * i) (IsHomogeneous.sum _ _ _ fun k hk => ?_) (swapR_aeval_isHomogeneous_five_vars d a b (i + 1)) fun h => ?_
    · have hk := Finset.mem_range.1 hk
      have h34 := (isHomogeneous_X ℝ (3 : Fin 5)).mul (isHomogeneous_X ℝ (4 : Fin 5))
      have hq := (isHomogeneous_X ℝ (0 : Fin 5)).mul
        (((isHomogeneous_X ℝ (3 : Fin 5)).add (isHomogeneous_X ℝ (4 : Fin 5))).sub (isHomogeneous_X ℝ (0 : Fin 5)))
      exact hom_cast ((h34.pow k).mul (hq.pow (i + 1 - 1 - k))) (by omega)
    · rw [swapR_eq_zero d a b (by omega), map_zero]

theorem eq_of_mul_eq_onLine_sub_onBase (d : ℕ) (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ)
    (h : (X 4 - X 0) * F = onLine d a b - onBase d a b) : F = (X 0 - X 3) * swapP d a b := by
  rw [onLine_sub_onBase_eq] at h
  have hne : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ≠ 0 :=
    sub_ne_zero.2 fun e => absurd (X_injective e) (by decide)
  exact mul_left_cancel₀ hne (by rw [h]; ring)

def fibPoly (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((m.choose j : ℝ) *
    ∫ t in (0 : ℝ)..1, (t * (1 - t)) ^ j * (1 - 4 * (t * (1 - t))) ^ (m - j)) * (X 0 ^ (2 * j) * X 1 ^ (m - j))

theorem aeval_fibPoly (m : ℕ) (a b : ℝ) :
    aeval ![a + b, a * b] (fibPoly m) = ∫ t in (0 : ℝ)..1, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m := by
  have hI : ∀ t : ℝ, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m = ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * (a + b) ^ (2 * j) * (a * b) ^ (m - j) * ((t * (1 - t)) ^ j * (1 - 4 * (t * (1 - t))) ^ (m - j)) := by
    intro t
    rw [show (a * t + b * (1 - t)) * (a * (1 - t) + b * t) =
      t * (1 - t) * (a + b) ^ 2 + (1 - 4 * (t * (1 - t))) * (a * b) by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_pow, ← pow_mul]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finsetSum fun j _ => by apply Continuous.intervalIntegrable; fun_prop]
  simp only [fibPoly, map_sum, map_mul, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring


def swapG : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ
  | 0, _, _ => 0
  | d + 1, a, b => C (1 / 2 : ℝ) * X 0 * ∑ i ∈ Finset.range (d + 3), ∑ k ∈ Finset.range i,
      (X 0 * X 1) ^ k * aeval ![X 0 + X 1, X 0 * X 1] (fibPoly (i - 1 - k)) * aeval ![X 0 + X 1, X 2] (swapR d a b i)


section Universal

open GlobalTheory.LineForm

private theorem aeval_aeval_two {σ S : Type} [CommRing S] [Algebra ℝ S] (f : σ → S) (u v : MvPolynomial σ ℝ)
    (p : MvPolynomial (Fin 2) ℝ) : aeval f (aeval ![u, v] p) = aeval ![aeval f u, aeval f v] p := by
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem sum_idx {M : Type} [AddCommMonoid M] (d : ℕ) (f : ℕ × ℕ → M) :
    ∑ x ∈ idx d, f x = ∑ i ∈ Finset.range (d + 3), ∑ k ∈ Finset.range i, f (i, k) := by
  rw [idx, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.1 hi
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem sum_monomial_coeffs_swap (d : ℕ) (a b : ℤ) : upperParabolic (idx d) expo (coefW (swapR d a b)) = swapP d a b := by
  rw [upperParabolic, sum_idx, swapP]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [coefW, expo, map_mul, map_pow, aeval_aeval_two, map_add, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dvd_downP_sub_baseT (d : ℕ) (R : ℕ → MvPolynomial (Fin 2) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      downP (idx d) expo (coefW R) - aeval ![X 1 + X 2, X 3, X 0] (baseT d R) := by
  rw [downP, baseT, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun x _ => ?_
  simp only [coefW, map_mul, map_pow, aeval_aeval_two, map_add, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (X 3 : MvPolynomial (Fin 4) ℝ) (X 1 * X 2) x.2
  refine ⟨-(c * aeval ![X 1 + X 2, X 3] (pm (expo x)) * aeval ![X 1 + X 2, X 0] (R x.1)), ?_⟩
  linear_combination (-(aeval ![X 1 + X 2, X 3] (pm (expo x)) * aeval ![X 1 + X 2, X 0] (R x.1))) * hc

theorem pm_aeval_isHomogeneous (m : ℕ) :
    (aeval ![X 0 + X 1, X 0 * X 1] (pm m) : MvPolynomial (Fin 3) ℝ).IsHomogeneous (2 * m) := by
  rw [pm, map_sum]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have h0 := isHomogeneous_X ℝ (0 : Fin 3)
  have h1 := isHomogeneous_X ℝ (1 : Fin 3)
  have h4 : (4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 0 := by
    have := isHomogeneous_C (Fin 3) (4 : ℝ)
    rwa [map_ofNat] at this
  rw [map_mul, map_mul, aeval_C, algebraMap_eq]
  simp only [map_mul, map_pow, map_sub, map_ofNat, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have hq : ((X 0 + X 1) ^ 2 - 4 * (X 0 * X 1) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
    (hom_cast ((h0.add h1).pow 2) (by omega)).sub (hom_cast (h4.mul (h0.mul h1)) (by omega))
  exact hom_cast (((isHomogeneous_C _ _).mul ((h0.mul h1).pow (m - j))).mul (hq.pow j)) (by omega)

theorem baseT_aeval_isHomogeneous (d : ℕ) (a b : ℤ) :
    (aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (swapR d a b)) : MvPolynomial (Fin 3) ℝ).IsHomogeneous d := by
  have h0 := isHomogeneous_X ℝ (0 : Fin 3)
  have h1 := isHomogeneous_X ℝ (1 : Fin 3)
  rw [baseT, map_sum]
  refine IsHomogeneous.sum _ _ _ fun x hx => ?_
  have hk : x.2 < x.1 := (Finset.mem_filter.1 hx).2
  simp only [map_mul, map_pow, aeval_aeval_two, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hR : (aeval ![X 0 + X 1, X 2] (swapR d a b x.1) : MvPolynomial (Fin 3) ℝ).IsHomogeneous
      (1 * (d + 2 - 2 * x.1)) :=
    (swapR_isHomogeneous d a b x.1).aeval _ (Fin.forall_fin_two.2 ⟨h0.add h1, isHomogeneous_X ℝ 2⟩)
  refine hom_mul_of (((h0.mul h1).pow x.2).mul (pm_aeval_isHomogeneous (expo x))) hR fun h => ?_
  rw [expo] at h
  rw [swapR_eq_zero d a b (by omega), map_zero]

theorem exists_swap_coefficients : ∃ R : ℕ → ℤ → ℤ → ℕ → MvPolynomial (Fin 2) ℝ, ∀ (d : ℕ) (a b : ℤ),
    (∀ F : MvPolynomial (Fin 5) ℝ, (X 4 - X 0) * F = onLine d a b - onBase d a b →
      F = (X 0 - X 3) * upperParabolic (idx d) expo (coefW (R d a b))) ∧
    (upperParabolic (idx d) expo (coefW (R d a b))).IsHomogeneous d ∧
    ((X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      downP (idx d) expo (coefW (R d a b)) - aeval ![X 1 + X 2, X 3, X 0] (baseT d (R d a b))) ∧
    (C (1 / 2 : ℝ) * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (R d a b)) :
      MvPolynomial (Fin 3) ℝ).IsHomogeneous (d + 1) := by
  refine ⟨swapR, fun d a b => ⟨fun F hF => ?_, ?_, dvd_downP_sub_baseT d _, ?_⟩⟩
  · rw [sum_monomial_coeffs_swap]; exact eq_of_mul_eq_onLine_sub_onBase d a b F hF
  · rw [sum_monomial_coeffs_swap]; exact swapP_isHomogeneous d a b
  · exact hom_cast (((isHomogeneous_C _ _).mul (isHomogeneous_X ℝ (0 : Fin 3))).mul
      (baseT_aeval_isHomogeneous d a b)) (by omega)

end Universal

end GlobalTheory.CovTest.SwapLine

end
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_combination_power : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := by
  first | exact @GlobalTheory.ChernTop.chernPart_comb_eq_part | exact GlobalTheory.ChernTop.chernPart_comb_eq_part | (intros; apply GlobalTheory.ChernTop.chernPart_comb_eq_part <;> assumption)
end

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm.PolarSum

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, Subalgebra.coe_add]

theorem evalF_smul {ι : Type} (w : ι → A.Pt → Ev n) (t : ℝ) (P : MvPolynomial ι ℝ) :
    evalF A w (t • P) = (t : ℂ) • evalF A w P := by
  funext x
  simp only [evalF, fld, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C,
    Pi.smul_apply, ← Algebra.smul_def, Subalgebra.coe_smul]
  rfl

theorem re_dens_loc_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (dens (A.loc ((t : ℂ) • α) i v)).re = t * (dens (A.loc α i v)).re := by
  have h : A.loc ((t : ℂ) • α) i v = (t : ℂ) • A.loc α i v := by
    unfold HolAtlas.loc; split_ifs
    · rfl
    · exact (smul_zero _).symm
  rw [h, ← Complex.re_ofReal_mul]
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

variable [MeasurableSpace M] [BorelSpace M]

theorem part_smul (t : ℝ) (α : A.Fld) (ε ε' : ℤˣ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal c • A.part α ε' := by
  have := ChernScale.glueMeas_restrict_eq A.e
    (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc ((t : ℂ) • α) i (A.e i y))).re))
    (ρ' := fun i y => ENNReal.ofReal ((ε' : ℤ) * (dens (A.loc α i (A.e i y))).re))
    (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top MeasurableSet.univ
    (fun i y _ _ => by beta_reduce; rw [re_dens_loc_smul, h, ENNReal.ofReal_mul hc])
  rw [Measure.restrict_univ, Measure.restrict_univ] at this
  exact this

theorem integrable_part_smul {g : M → ℝ} (t : ℝ) {α : A.Fld} (h : ∀ ε : ℤˣ, Integrable g (A.part α ε)) (ε : ℤˣ) :
    Integrable g (A.part ((t : ℂ) • α) ε) := by
  rcases le_total 0 t with ht | ht
  · rw [part_smul A t α ε ε t ht fun x => by ring]
    exact (h ε).smul_measure ENNReal.ofReal_ne_top
  · rw [part_smul A t α ε (-ε) (-t) (neg_nonneg.2 ht) fun x => by rw [Units.val_neg, Int.cast_neg]; ring]
    exact (h _).smul_measure ENNReal.ofReal_ne_top

theorem part_zero_smul (α : A.Fld) (ε : ℤˣ) : A.part (((0 : ℝ) : ℂ) • α) ε = 0 := by
  rw [part_smul A 0 α ε ε 0 le_rfl fun x => by ring, ENNReal.ofReal_zero, zero_smul]

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

theorem wInt_evalF_sum {ι κ : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (g : M → ℝ)
    (P : κ → MvPolynomial ι ℝ) (c : κ → ℝ) (s : Finset κ)
    (h : ∀ a ∈ s, ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (P a)) ε)) :
    (∀ ε : ℤˣ, Integrable g (A.part (evalF A w (∑ a ∈ s, c a • P a)) ε)) ∧
      wInt A g (evalF A w (∑ a ∈ s, c a • P a)) = ∑ a ∈ s, c a * wInt A g (evalF A w (P a)) := by
  have hF : ∀ Q, A.IsForm (evalF A w Q) := fun Q => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1
  obtain ⟨-, hadd, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  induction s using Finset.induction_on with
  | empty =>
    have e : evalF A w 0 = ((0 : ℝ) : ℂ) • evalF A w 0 := by rw [← evalF_smul, zero_smul]
    simp only [Finset.sum_empty]
    rw [e]
    refine ⟨fun ε => ?_, ?_⟩
    · rw [part_zero_smul]; exact integrable_zero_measure
    · rw [hsm g 0 _ (hF _), zero_mul]
  | insert a s ha ih =>
    obtain ⟨i₁, i₂⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have j₁ : ∀ ε : ℤˣ, Integrable g (A.part (evalF A w (c a • P a)) ε) := by
      rw [evalF_smul]
      exact integrable_part_smul A (c a) (h a (Finset.mem_insert_self a s))
    obtain ⟨k₁, k₂⟩ := hadd g _ _ (hF _) (hF _) j₁ i₁
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evalF_add]
    refine ⟨k₁, ?_⟩
    rw [k₂, i₂, evalF_smul, hsm g _ _ (hF _)]

end Manifold

theorem wInt_sum_lin_pow : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  intro k _ X p D hX σ ι _ L g s c h
  haveI := hX.toIsArithVar.isIntegral
  obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.IsArithVar.finite_emb_and_topology hX.toIsArithVar).2 σ
  exact (wInt_evalF_sum (hX.atlas σ) (fun i => c1F hX σ (L i))
    (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1) g
    (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ D) c s h).2

end GlobalTheory.LineForm.PolarSum
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_chern_combination : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  atlas_forward_decl GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archIntegrable_regular_variety : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsRegVar p D →
    ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  first | exact @GlobalTheory.LogNormInt.archIntegrable | exact GlobalTheory.LogNormInt.archIntegrable | (intros; apply GlobalTheory.LogNormInt.archIntegrable <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.ChernPoly

theorem chernPart_offSupp_null : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    ∀ (σ : k →+* ℂ) (N : HermLB p) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    {M : LB Y} (φ : Weight p σ M) (ε : ℤˣ), φ.chernPart D ε (offSupp p σ (N.div hr))ᶜ = 0 := by
  intro k _ Y _ p D hp σ N r hr M φ ε
  have e : (offSupp p σ (N.div hr))ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((N.div hr).supp : Set Y)} := by
    ext y
    simp only [Set.mem_compl_iff, mem_offSupp, not_not]
    rfl
  rw [e]
  exact GlobalTheory.ChernNull.chernPart_over_closed hp _ (N.div hr).supp.isClosed
    (CartierDiv.genericPoint_notMem_supp _) σ φ ε

theorem chernPart_comb_eq_part : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := GlobalTheory.T.chern_part_combination_power

theorem wInt_sum_lin_pow : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := GlobalTheory.T.weighted_integral_chern_combination

theorem archIntegrable_of_isRegVar : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsRegVar p D →
    ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := GlobalTheory.T.archIntegrable_regular_variety

theorem archInt_sum_eq_wInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (N : HermLB p)
    (r : N.B.ι → X.functionFieldˣ) (hr : IsRatSec N.B r) (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
    (∀ σ, ∀ y ∈ offSupp p σ (N.div hr), logNorm (N.φ σ) r y = g σ y) →
    ∀ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
      ∑ n ∈ s, c n * (comb L n).archInt N D hr =
        ∑ᶠ σ : k →+* ℂ, wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) := by
  intro k _ X _ p D hX ι _ L N r hr g hg s c
  haveI : Finite (k →+* ℂ) := (GlobalTheory.T.arith_var_complex_points_compact hX.toIsArithVar).1
  haveI := Fintype.ofFinite (k →+* ℂ)
  have key : ∀ (n : ι → ℤ) (σ : k →+* ℂ),
      ((comb L n).φ σ).chernInt D (offSupp p σ (N.div hr)) (logNorm (N.φ σ) r) =
        wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ∧
      ∀ ε : ℤˣ, Integrable (g σ)
        ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε) := by
    intro n σ
    have hae : ∀ ε : ℤˣ, ∀ᵐ y ∂((comb L n).φ σ).chernPart D ε, y ∈ offSupp p σ (N.div hr) := fun ε =>
      measure_eq_zero_iff_ae_notMem.1
        (chernPart_offSupp_null hX.toIsArithVar σ N hr _ ε) |>.mono fun y hy => by simpa using hy
    have hres : ∀ ε : ℤˣ, (((comb L n).φ σ).chernPart D ε).restrict (offSupp p σ (N.div hr)) =
        ((comb L n).φ σ).chernPart D ε := fun ε => Measure.restrict_eq_self_of_ae_mem (hae ε)
    have hfg : ∀ ε : ℤˣ, logNorm (N.φ σ) r =ᵐ[((comb L n).φ σ).chernPart D ε] g σ := fun ε =>
      (hae ε).mono fun y hy => hg σ y hy
    have hint := archIntegrable_of_isRegVar hX (comb L n) N hr σ
    refine ⟨?_, fun ε => ?_⟩
    · rw [Weight.chernInt, hres, hres, integral_congr_ae (hfg 1), integral_congr_ae (hfg (-1)), wInt,
        chernPart_comb_eq_part hX σ L n, chernPart_comb_eq_part hX σ L n]
    · rw [← chernPart_comb_eq_part hX σ L n]
      have h1 : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr)) (((comb L n).φ σ).chernPart D ε) := by
        rcases Int.units_eq_one_or ε with rfl | rfl
        exacts [hint.1, hint.2]
      rw [IntegrableOn, hres] at h1
      exact h1.congr (hfg ε)
  have hL : ∀ n : ι → ℤ, (comb L n).archInt N D hr = ∑ σ, wInt (hX.atlas σ) (g σ)
      (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := fun n => by
    rw [HermLB.archInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => (key n σ).1
  rw [finsum_eq_sum_of_fintype]
  simp only [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [wInt_sum_lin_pow hX σ L (g σ) s c fun n _ ε => (key n σ).2 ε]

end GlobalTheory.ChernPoly
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_intersection_combination_log_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (N : HermLB p)
    (r : N.B.ι → X.functionFieldˣ) (hr : IsRatSec N.B r) (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
    (∀ σ, ∀ y ∈ offSupp p σ (N.div hr), logNorm (N.φ σ) r y = g σ y) →
    ∀ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
      ∑ n ∈ s, c n * (comb L n).archInt N D hr =
        ∑ᶠ σ : k →+* ℂ, wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) := by
  atlas_forward_decl GlobalTheory.ChernPoly.archInt_sum_eq_wInt
end

section
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_symmetric_mul_difference : ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) = (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  first | exact @GlobalTheory.LineForm.aeval_hs_mul_sub | exact GlobalTheory.LineForm.aeval_hs_mul_sub | (intros; apply GlobalTheory.LineForm.aeval_hs_mul_sub <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.FibVan

theorem esymm_sub_injective :
    Function.Injective (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) := by
  have e : (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) =
      (symmetricSubalgebra (Fin 2) ℝ).val.comp (esymmAlgHom (Fin 2) ℝ 2) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i
    · simp [esymmAlgHom, esymm, Finset.powersetCard_one, Fin.sum_univ_two]
    · have : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by decide
      simp [esymmAlgHom, esymm, Fin.prod_univ_two, this]
  rw [e]
  exact Subtype.val_injective.comp (esymmAlgHom_fin_injective ℝ le_rfl)

theorem X_sub_X_ne_zero : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  intro h
  have := congrArg (eval ![1, 0]) h
  simp at this

theorem hs_roots (k : ℕ) : aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) =
    (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := GlobalTheory.T.complete_symmetric_mul_difference k

theorem sum_hs_eq_zero (m' : ℕ) : ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
    X 0 ^ (m' + 1 - i) = (0 : MvPolynomial (Fin 2) ℝ) := by
  apply esymm_sub_injective
  rw [map_zero]
  refine (mul_left_injective₀ X_sub_X_ne_zero) ?_
  simp only [zero_mul, map_sum, Finset.sum_mul]
  have key : ∀ c : MvPolynomial (Fin 2) ℝ, ∑ i ∈ Finset.range (m' + 2), (-c) ^ i * (X 0 + X 1) ^ (m' + 1 - i) *
      (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) = (-c + (X 0 + X 1)) ^ (m' + 1) := fun c => (add_pow _ _ _).symm
  have h0 := key (X 0)
  have h1 := key (X 1)
  rw [show -X 0 + (X 0 + X 1) = (X 1 : MvPolynomial (Fin 2) ℝ) by ring] at h0
  rw [show -X 1 + (X 0 + X 1) = (X 0 : MvPolynomial (Fin 2) ℝ) by ring] at h1
  have e : ∀ i ∈ Finset.range (m' + 2), aeval ![X 0 + X 1, X 0 * X 1]
      (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) * X 0 ^ (m' + 1 - i)) * (X 0 - X 1) =
      X 0 ^ (m' + 1) * ((-X 0) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) -
      X 1 ^ (m' + 1) * ((-X 1) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) := by
    intro i _
    have hr := hs_roots (m' + i)
    simp only [map_mul, map_pow, aeval_C, aeval_X, algebraMap_eq, map_neg, map_one, map_natCast, neg_pow (X 0 : MvPolynomial (Fin 2) ℝ),
      neg_pow (X 1 : MvPolynomial (Fin 2) ℝ), Matrix.cons_val_zero]
    linear_combination ((-1 : MvPolynomial (Fin 2) ℝ) ^ i * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) * (X 0 + X 1) ^ (m' + 1 - i)) * hr
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1]
  ring

end GlobalTheory.FibVan

noncomputable section

namespace GlobalTheory.FibVan

section Gen
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fldHom : (A.Pt → Ev n) →ₐ[ℂ] A.Fld := AlgHom.compLeft (Subalgebra.center ℂ (Alt n)).val A.Pt

theorem fldHom_apply (u : A.Pt → Ev n) : fldHom A u = fld A u := rfl

theorem fldHom_comm (u : A.Pt → Ev n) (β : A.Fld) : β * fldHom A u = fldHom A u * β := by
  funext x
  exact Subalgebra.mem_center_iff.mp (u x).2 (β x)

def xi {ι : Type} (w : ι → A.Pt → Ev n) : MvPolynomial ι ℝ →+* A.Fld :=
  (fldHom A).toRingHom.comp ((aeval w).toRingHom.comp (MvPolynomial.map (algebraMap ℝ ℂ)))

theorem xi_apply {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) :
    xi A w Q = fldHom A (aeval w (Q.map (algebraMap ℝ ℂ))) := rfl

theorem evalF_eq_xi {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) : evalF A w Q = xi A w Q := by
  funext x
  rw [xi_apply, fldHom_apply]
  show ((aeval (fun i => w i x) (Q.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = ((aeval w (Q.map (algebraMap ℝ ℂ)) x : Ev n) : Alt n)
  congr 1
  rw [show (aeval w (Q.map (algebraMap ℝ ℂ)) x) = Pi.evalAlgHom ℂ (fun _ => Ev n) x (aeval w (Q.map (algebraMap ℝ ℂ))) from rfl,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem xi_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : xi A w (X i) = fldHom A (w i) := by
  simp [xi_apply]

theorem xi_C {ι : Type} (w : ι → A.Pt → Ev n) (r : ℝ) : xi A w (C r) = algebraMap ℂ A.Fld (r : ℂ) := by
  simp [xi_apply]

theorem isForm_xi {ι : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (Q : MvPolynomial ι ℝ) :
    A.IsForm (xi A w Q) := by
  rw [← evalF_eq_xi]
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1

theorem isForm_mul {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α * β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).2.1

theorem isForm_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α + β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).1

theorem isForm_smul (c : ℂ) {α : A.Fld} (hα : A.IsForm α) : A.IsForm (c • α) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 c α α hα hα).2.2.1

theorem isForm_one : A.IsForm 1 := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1

theorem isForm_zero : A.IsForm 0 := by simpa using isForm_smul A 0 (isForm_one A)

theorem isForm_pow {α : A.Fld} (hα : A.IsForm α) (j : ℕ) : A.IsForm (α ^ j) := by
  induction j with
  | zero => simpa using isForm_one A
  | succ j ih => rw [pow_succ]; exact isForm_mul A ih hα

theorem isForm_sum {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.IsForm (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isForm_zero A
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isForm_add A (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Gen

section Lin
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

theorem integral_add' {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have hi : ∀ γ : A.Fld, A.IsForm γ → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part γ ε) := fun γ hγ ε => by
    haveI := hfin γ hγ ε
    exact integrable_const _
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  exact (hadd _ α β hα hβ (hi α hα) (hi β hβ)).2

theorem integral_smul' (t : ℝ) {α : A.Fld} (hα : A.IsForm α) : A.integral ((t : ℂ) • α) = t * A.integral α := by
  obtain ⟨-, -, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact hsm _ t α hα

theorem integral_zero' : A.integral 0 = 0 := by
  have := integral_smul' A 0 (isForm_one A)
  simpa using this

theorem integral_sum' {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.integral (∑ i ∈ s, f i) = ∑ i ∈ s, A.integral (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using integral_zero' A
  | insert a s ha ih =>
    have hs : A.IsForm (∑ i ∈ s, f i) := isForm_sum A s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add' A (hf a (by simp)) hs,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end Lin

end GlobalTheory.FibVan

end

noncomputable section

namespace GlobalTheory.FibVan

theorem pow_succ_of_sq_zero' {R : Type} [CommRing R] (t ω : R) (n : ℕ) :
    ∃ r : R, t ^ (n + 1) = (t + ω) ^ (n + 1) - ((n : R) + 1) * (ω * (t + ω) ^ n) + ω * ω * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨((n : R) + 1) * (t + ω) ^ n + t * r, ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

theorem expand_pow {R : Type} [CommRing R] (t e : R) (m : ℕ) :
    (t * (e - t)) ^ m = ∑ i ∈ Finset.range (m + 1), ((-1) ^ i * (m.choose i : R)) * (t ^ (m + i) * e ^ (m - i)) := by
  rw [mul_pow, show e - t = -t + e by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]
  ring

def pullHom {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p) :
    (hB.atlas σ).Fld →+* (hY.atlas σ).Fld where
  toFun := pullF hB hY σ π w
  map_one' := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).1
  map_mul' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).2.1
  map_zero' := by
    have := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
      ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 0 0).2.2.1
    simp only [zero_smul] at this
    exact this
  map_add' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).1

section Pull
variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p)

theorem pullHom_apply (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w α = pullF hB hY σ π w α := rfl

theorem pullHom_smul (c : ℂ) (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w (c • α) = c • pullHom hB hY σ π w α :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 c α α).2.2.1

theorem pullHom_algebraMap (c : ℂ) : pullHom hB hY σ π w (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  rw [Algebra.algebraMap_eq_smul_one, pullHom_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

theorem isForm_pullHom {α : (hB.atlas σ).Fld} (hα : (hB.atlas σ).IsForm α) : (hY.atlas σ).IsForm (pullHom hB hY σ π w α) :=
  ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α α).2.2.2 hα).1

end Pull

theorem fibre_integral_vanish : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (pullF hB hY σ π w φ * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ phi hφ ι s m W
  haveI := hB.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  haveI := hY.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have glob := fun χ hχ n => GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ χ hχ n
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨bB1, bB2, -⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨-, hpc1, -⟩ := (GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p (d + 1) hY π w
  set P := pullHom hB hY σ π w with hP
  set x5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx5
  set f4 : Fin 4 → (hB.atlas σ).Pt → Ev d := fam4 hB σ H flB A with hf4
  set om : (hY.atlas σ).Pt → Ev (d + 1) := omF hY σ (h.pull π w) fl with hom
  have hom2 : om * om = 0 := (bY2 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1
  have fx5 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x5 i)) := fun i => (bY1 _ (fam5 π w H flB fl A i)).1.1
  have ff4 : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (f4 i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have fom : (hY.atlas σ).IsForm (fld (hY.atlas σ) om) := (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1

  have hbr : ∀ Q : MvPolynomial (Fin 3) ℝ, xi (hY.atlas σ) x5 (aeval ![X 2, X 3, X 4] Q) = P (xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] Q)) := by
    intro Q
    have e : (xi (hY.atlas σ) x5).comp (aeval ![X 2, X 3, X 4] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toRingHom =
        P.comp ((xi (hB.atlas σ) f4).comp (aeval ![X 0, X 1, X 2] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ).toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
          algebraMap_eq, xi_C]
        rw [pullHom_algebraMap]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        fin_cases j
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 A
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
        · simp only [Fin.reduceFinMk, Matrix.cons_val, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
    exact congrArg (fun f => f Q) e

  have hc6 : ∀ (Q : MvPolynomial (Fin 6) ℝ) (β : (hY.atlas σ).Fld), β * xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q =
      xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q * β := fun Q β => fldHom_comm (hY.atlas σ) _ β
  obtain ⟨x6, hx6⟩ : ∃ x6 : Fin 6 → (hY.atlas σ).Pt → Ev (d + 1), x6 = Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om := ⟨_, rfl⟩
  rw [← hx6] at hc6
  have hx6i : ∀ i : Fin 5, x6 i.castSucc = x5 i := fun i => by rw [hx6]; exact Fin.snoc_castSucc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _ _
  have h5 : x6 5 = om := by rw [hx6]; exact Fin.snoc_last (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _
  have f6 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x6 i)) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show x6 (Fin.last 5) = om from h5]; exact fom
    · rw [hx6i]; exact fx5 j
  have xi6_0 : xi (hY.atlas σ) x6 (X 0) = fld (hY.atlas σ) (x5 0) := by rw [xi_X, fldHom_apply, show x6 0 = x5 0 from hx6i 0]
  have xi6_5 : xi (hY.atlas σ) x6 (X 5) = fld (hY.atlas σ) om := by rw [xi_X, fldHom_apply, h5]
  have xi6_sq : xi (hY.atlas σ) x6 (X 5 * X 5) = 0 := by
    rw [map_mul, xi_X, h5, ← map_mul]
    exact (congrArg (fldHom (hY.atlas σ)) hom2).trans (map_zero _)
  have hren : ∀ Q : MvPolynomial (Fin 5) ℝ, xi (hY.atlas σ) x5 Q = xi (hY.atlas σ) x6 (rename Fin.castSucc Q) := by
    intro Q
    have e : xi (hY.atlas σ) x5 = (xi (hY.atlas σ) x6).comp (rename Fin.castSucc : MvPolynomial (Fin 5) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp [xi_C]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, xi_X, hx6i]
    exact congrArg (fun f => f Q) e
  have heps6 : xi (hY.atlas σ) x6 (X 3 + X 4) = P (xi (hB.atlas σ) f4 (X 1 + X 2)) := by
    have hh := hbr (X 1 + X 2)
    have l : aeval ![X 2, X 3, X 4] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 3 + X 4 : MvPolynomial (Fin 5) ℝ) := by simp
    have r : aeval ![X 0, X 1, X 2] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 1 + X 2 : MvPolynomial (Fin 4) ℝ) := by simp
    rw [l, r, hren] at hh
    rw [← hh]
    congr 1
    simp only [map_add, rename_X]
    rfl
  have fε : (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (X 1 + X 2)) := isForm_xi (hB.atlas σ) f4 ff4 _
  have KY1 : ∀ (n : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ) =
      -(hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
    intro n χ hχ
    obtain ⟨R, hR⟩ := pow_succ_of_sq_zero' (X 0 : MvPolynomial (Fin 6) ℝ) (X 5) n
    have g1 : (hY.atlas σ).integral ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) = 0 := (glob χ hχ (n + 1)).1
    have g2 : (hY.atlas σ).integral (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) =
        1 / (n + 1 : ℝ) * (hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
      rw [← evalF_eq_xi]; exact (glob χ hχ n).2
    have key : xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ = (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ +
        ((-((n : ℝ) + 1) : ℝ) : ℂ) • (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) := by
      rw [hR, map_add, map_mul (xi (hY.atlas σ) x6) (X 5 * X 5) R, xi6_sq, zero_mul, add_zero]
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_one, xi6_0, xi6_5]
      rw [Algebra.smul_def, hP, pullHom_apply]
      simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, map_neg, map_add,
        map_natCast, map_one]
      noncomm_ring
    have f1 : (hY.atlas σ).IsForm ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _) (isForm_pullHom hB hY σ π w hχ)
    have f2 : (hY.atlas σ).IsForm (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_mul (hY.atlas σ) fom (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _)) (isForm_pullHom hB hY σ π w hχ)
    rw [key, integral_add' (hY.atlas σ) f1 (isForm_smul (hY.atlas σ) _ f2), integral_smul' (hY.atlas σ) _ f2, g1, g2]
    field_simp
    ring
  have KY : ∀ (j : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ j) * P χ) = 0 := by
    intro j χ hχ
    rcases j with _ | m'
    · have := (glob χ hχ 0).1
      simpa [hP, pullHom_apply] using this
    · have hexp : (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ (m' + 1) =
          ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i)) := by
        rw [expand_pow]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show m' + 1 + i = m' + i + 1 by omega]
        simp [map_mul, map_pow, map_neg, map_natCast]
      have hterm : ∀ i ∈ Finset.range (m' + 2), xi (hY.atlas σ) x6 (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) *
          (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i))) * P χ = ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) := by
        intro i _
        rw [map_mul (xi (hY.atlas σ) x6) (C _) _, map_mul (xi (hY.atlas σ) x6) (X 0 ^ _) _, map_pow (xi (hY.atlas σ) x6) (X 3 + X 4), heps6, xi_C, Algebra.smul_def,
          map_mul P, map_pow P]
        simp only [mul_assoc]
      have fZ : ∀ i ∈ Finset.range (m' + 2), (hY.atlas σ).IsForm (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hY.atlas σ) (isForm_xi (hY.atlas σ) x6 f6 _)
          (isForm_pullHom hB hY σ π w (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ))
      rw [hexp, map_sum, Finset.sum_mul, Finset.sum_congr rfl hterm,
        integral_sum' (hY.atlas σ) _ (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
          (fun i hi => isForm_smul (hY.atlas σ) _ (fZ i hi))]
      rw [Finset.sum_congr rfl (fun i hi => by rw [integral_smul' (hY.atlas σ) _ (fZ i hi), KY1 _ _ (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)])]
      have fB : ∀ i ∈ Finset.range (m' + 2), (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) *
          (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hB.atlas σ) (isForm_xi (hB.atlas σ) f4 ff4 _) (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)
      have hsumB : ∑ i ∈ Finset.range (m' + 2), ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) =
          xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
            X 0 ^ (m' + 1 - i))) * χ := by
        rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, algebraMap_eq, xi_C,
          Algebra.smul_def]
        simp only [mul_assoc]
      have h0 := integral_sum' (hB.atlas σ) (Finset.range (m' + 2)) (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
        (fun i hi => isForm_smul (hB.atlas σ) _ (fB i hi))
      rw [hsumB, sum_hs_eq_zero, map_zero, map_zero, zero_mul, integral_zero'] at h0
      rw [Finset.sum_congr rfl (fun i hi => integral_smul' (hB.atlas σ) _ (fB i hi))] at h0
      simp only [mul_neg, Finset.sum_neg_distrib, ← h0, neg_zero]
  rw [evalF_eq_xi, upperParabolic, map_sum, Finset.mul_sum]
  rw [integral_sum' (hY.atlas σ) s (fun x => pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)))
    (fun x _ => isForm_mul (hY.atlas σ) (isForm_pullHom hB hY σ π w hφ) (isForm_xi (hY.atlas σ) x5 fx5 _))]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hA : rename Fin.castSucc ((X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) ^ m x) =
      (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ m x := by
    simp only [map_pow, map_mul, map_sub, map_add, rename_X]
    rfl
  have hx : pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)) =
      xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ m x) * P (phi * xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] (W x))) := by
    rw [map_mul, hbr, hren, hA, ← mul_assoc, hc6, mul_assoc, map_mul P]
    rfl
  rw [hx]
  exact KY _ _ (isForm_mul (hB.atlas σ) hφ (isForm_xi (hB.atlas σ) f4 ff4 _))

end GlobalTheory.FibVan

end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_second : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (pullF hB hY σ π w φ * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = 0 := by
  atlas_forward_decl GlobalTheory.FibVan.fibre_integral_vanish
end

section
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.LineForm

namespace GlobalTheory.LineForm.PolyId

def tm (n j : ℕ) : MvPolynomial (Fin 2) ℝ := C ((-1) ^ j * ((n - j).choose j : ℝ)) * X 0 ^ (n - 2 * j) * X 1 ^ j

theorem tm_eq_zero (n j : ℕ) (h : n < j) : tm n j = 0 := by
  simp [tm, Nat.choose_eq_zero_of_lt (show n - j < j by omega)]

theorem hs_eq (n K : ℕ) (hK : n + 1 ≤ K) : hs n = ∑ j ∈ Finset.range K, tm n j := by
  unfold hs
  exact Finset.sum_subset (Finset.range_mono hK) (fun j hj hj' => by
    simp only [Finset.mem_range] at hj hj'; exact tm_eq_zero n j (by omega))

theorem pascal (n j : ℕ) : (n + 2 - (j + 1)).choose (j + 1) = (n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) := by
  rcases le_or_gt j n with h | h
  · rw [show n + 2 - (j + 1) = (n - j) + 1 by omega, show n + 1 - (j + 1) = n - j by omega, Nat.choose_succ_succ']
  · rw [show n + 2 - (j + 1) = 0 by omega, show n - j = 0 by omega, show n + 1 - (j + 1) = 0 by omega,
      Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]

theorem tm_rec (n j : ℕ) : tm (n + 2) (j + 1) = X 0 * tm (n + 1) (j + 1) - X 1 * tm n j := by
  have hb : C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ (n - 2 * j) =
      X 0 * (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (n + 1 - 2 * (j + 1))) := by
    by_cases h : 2 * j + 1 ≤ n
    · rw [show n - 2 * j = (n + 1 - 2 * (j + 1)) + 1 by omega, pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 - (j + 1) < j + 1)]; simp
  have hC : C ((-1) ^ (j + 1) * ((((n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) : ℕ)) : ℝ)) =
      (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) - C ((-1) ^ j * ((n - j).choose j : ℝ)) :
        MvPolynomial (Fin 2) ℝ) := by
    rw [← C_sub]; congr 1; push_cast; ring
  simp only [tm]
  rw [pascal, show n + 2 - 2 * (j + 1) = n - 2 * j by omega, hC]
  linear_combination X 1 ^ (j + 1) * hb

theorem hs_rec (n : ℕ) : hs (n + 2) = X 0 * hs (n + 1) - X 1 * hs n := by
  rw [hs_eq (n + 2) (n + 2 + 1) le_rfl, hs_eq (n + 1) (n + 2 + 1) (by omega), hs_eq n (n + 2) (by omega),
    Finset.sum_range_succ', Finset.sum_range_succ' (fun j => tm (n + 1) j)]
  simp_rw [tm_rec]
  rw [Finset.sum_sub_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h0 : tm (n + 2) 0 = X 0 * tm (n + 1) 0 := by simp [tm]; ring
  rw [h0]; ring

theorem eval_hs_mul (a b : ℝ) (n : ℕ) :
    (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) := by
  have key : ∀ n : ℕ, (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) ∧
      (a - b) * eval ![a + b, a * b] (hs (n + 1)) = a ^ (n + 2) - b ^ (n + 2) := by
    intro n
    induction n with
    | zero => constructor <;> simp [hs, Finset.sum_range_succ] <;> ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hs_rec]
      simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (a + b) * ih.2 - a * b * ih.1
  exact (key n).1

theorem integral_affine (a b : ℝ) (hab : a ≠ b) (n : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n = (a ^ (n + 1) - b ^ (n + 1)) / (((n : ℝ) + 1) * (a - b)) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have e : (fun t : ℝ => (t * a + (1 - t) * b) ^ n) = fun t => (fun x : ℝ => x ^ n) ((a - b) * t + b) := by
    funext t; ring
  rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ n) hd, integral_pow]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem beta_eq (j : ℕ) :
    ∫ t in (0:ℝ)..1, t ^ j * (1 - t) ^ j = (j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial := by
  have h : ((j : ℝ) + j + 1) * ((j + j).choose j : ℝ) * ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j = 1 := ReciprocityTheory.GeometryOfNumbersTheory.bI_closed j j
  have hc := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + j by omega)
  rw [show j + j - j = j by omega] at hc
  have hc' : ((j + j).choose j : ℝ) * j.factorial * j.factorial = (j + j).factorial := by exact_mod_cast hc
  have hf : ((2 * j + 1).factorial : ℝ) = (2 * (j : ℝ) + 1) * (j + j).factorial := by
    rw [show 2 * j + 1 = (j + j) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have hpos : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hpos, hf]
  change ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j * _ = _
  linear_combination (-(ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j) * (2 * (j : ℝ) + 1)) * hc' + ((j.factorial : ℝ) * j.factorial) * h

theorem eval_lhs (a b : ℝ) (hab : a ≠ b) (m : ℕ) :
    eval ![a + b, a * b] (∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j))
      = ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m := by
  have hE : ∀ n : ℕ, eval ![a + b, a * b] (hs n) = ((n : ℝ) + 1) * ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n := by
    intro n
    rw [integral_affine a b hab n]
    have h := eval_hs_mul a b n
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    linear_combination h
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (m.choose j : ℝ) * (a + b) ^ (m - j) * (t * a + (1 - t) * b) ^ (m + j) := by
    intro t
    rw [show a + b - (t * a + (1 - t) * b) = -(t * a + (1 - t) * b) + (a + b) by ring, add_pow (-(t * a + (1 - t) * b)) (a + b) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow]; ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [map_sum, map_mul, eval_C, map_pow, eval_X, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp only [Matrix.cons_val_zero]
  have hp : (m : ℝ) + j + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

theorem eval_rhs (a b : ℝ) (m : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m = eval ![a + b, a * b] (pm m) := by
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (a * b) ^ (m - j) * ((a + b) ^ 2 - 4 * (a * b)) ^ j) *
        (t ^ j * (1 - t) ^ j) := by
    intro t
    rw [← mul_pow, show (t * a + (1 - t) * b) * (a + b - (t * a + (1 - t) * b)) =
      t * (1 - t) * ((a + b) ^ 2 - 4 * (a * b)) + a * b by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, mul_pow]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, beta_eq]
  simp
  ring

theorem eval_map_aeval (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℂ) :
    eval z ((aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ).map (algebraMap ℝ ℂ)) =
      eval ![z 0 + z 1, z 0 * z 1] (P.map (algebraMap ℝ ℂ)) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, map_X, eval_X]
    fin_cases i <;> simp

theorem eval_aeval_sym (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    eval x (aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ) = eval ![x 0 + x 1, x 0 * x 1] P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    fin_cases i <;> simp

theorem eq_zero_of_symm_real (P : MvPolynomial (Fin 2) ℝ) (h : ∀ a b : ℝ, a ≠ b → eval ![a + b, a * b] P = 0) :
    P = 0 := by
  set Q : MvPolynomial (Fin 2) ℝ := aeval ![X 0 + X 1, X 0 * X 1] P with hQ
  have hQe : ∀ x : Fin 2 → ℝ, eval x Q = eval ![x 0 + x 1, x 0 * x 1] P := by
    intro x
    rw [hQ, eval_aeval_sym]
  have hXQ : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) * Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, hQe]
    by_cases hx : x 0 = x 1
    · simp [hx]
    · simp [h _ _ hx]
  have hX : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h0
    have := congrArg (eval ![1, 0]) h0
    simp at this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hXQ).resolve_left hX
  have hPm : P.map (algebraMap ℝ ℂ) = 0 := by
    refine GlobalTheory.FibLine.eq_zero_of_eval_symm _ fun a b => ?_
    have := eval_map_aeval P ![a, b]
    rw [← hQ, hQ0] at this
    simpa using this.symm
  exact MvPolynomial.map_injective _ (algebraMap ℝ ℂ).injective (by simpa using hPm)

end GlobalTheory.LineForm.PolyId

namespace GlobalTheory.LineForm

open PolyId in

theorem sum_choose_hs_eq_pm : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1),
    C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  intro m
  rw [← sub_eq_zero]
  refine eq_zero_of_symm_real _ fun a b hab => ?_
  rw [map_sub, eval_lhs a b hab m, eval_rhs a b m, sub_self]

end GlobalTheory.LineForm
end
end

open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_binomial_sum_eq_polynomial : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  atlas_forward_decl GlobalTheory.LineForm.sum_choose_hs_eq_pm
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.ChernFibre

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fldA : (A.Pt → Ev n) →ₐ[ℂ] A.Fld :=
  AlgHom.pi fun x => (Subalgebra.center ℂ (Alt n)).val.comp (Pi.evalAlgHom ℂ (fun _ => Ev n) x)

theorem fld_eq (w : A.Pt → Ev n) : fld A w = fldA A w := rfl

theorem evalF_eq {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) :
    evalF A w P = fldA A (aeval w P) := by
  funext x
  have h1 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (f := w) (Pi.evalAlgHom ℂ (fun _ => Ev n) x))
    (P.map (algebraMap ℝ ℂ))
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at h1
  simp only [evalF, fld, fldA, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, Subalgebra.coe_val]
  rw [← h1, MvPolynomial.aeval_map_algebraMap]

theorem aeval_aeval' {S : Type} [CommRing S] [Algebra ℝ S] {ι κ : Type} (f : κ → S) (v : ι → MvPolynomial κ ℝ)
    (P : MvPolynomial ι ℝ) : aeval f (aeval v P) = aeval (fun i => aeval f (v i)) P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

theorem evalF_C {ι : Type} (w : ι → A.Pt → Ev n) (r : ℝ) : evalF A w (C r) = (r : ℂ) • (1 : A.Fld) := by
  rw [evalF_eq, aeval_C, IsScalarTower.algebraMap_apply ℝ ℂ (A.Pt → Ev n), AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]
  rfl

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  simp only [evalF_eq, map_add]

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  simp only [evalF_eq, map_mul]

theorem evalF_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : evalF A w (X i) = fld A (w i) := by
  rw [evalF_eq, aeval_X]; rfl

theorem isForm_pow {α : A.Fld} (h : A.IsForm α) (N : ℕ) : A.IsForm (α ^ N) := by
  induction N with
  | zero => simpa using (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1
  | succ N ih => rw [pow_succ]; exact (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 1 _ _ ih h).2.1)

theorem integral_sum_smul [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    {κ : Type} (S : Finset κ) (r : κ → ℝ) (α : κ → A.Fld) (h : ∀ a ∈ S, A.IsForm (α a)) :
    A.IsForm (∑ a ∈ S, ((r a : ℝ) : ℂ) • α a) ∧
      A.integral (∑ a ∈ S, ((r a : ℝ) : ℂ) • α a) = ∑ a ∈ S, r a * A.integral (α a) := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have F := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  have hint : ∀ β : A.Fld, A.IsForm β → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part β ε) := by
    intro β hβ ε
    haveI := L.1 β hβ ε
    exact integrable_const _
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (F.2.1 0 1 1 F.1 F.1).2.2.1, ?_⟩
    have h0 := L.2.2.1 (fun _ => 1) 0 1 F.1
    simp only [Complex.ofReal_zero, zero_smul, zero_mul, wInt_one] at h0
    simpa using h0
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have hs : A.IsForm (((r a : ℝ) : ℂ) • α a) := (F.2.1 _ (α a) (α a) (h a (Finset.mem_insert_self a S))
      (h a (Finset.mem_insert_self a S))).2.2.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨(F.2.1 1 _ _ hs ih1).1, ?_⟩
    have e := (L.2.1 (fun _ => 1) _ _ hs ih1 (hint _ hs) (hint _ ih1)).2
    rw [wInt_one, wInt_one, wInt_one] at e
    rw [e, ih2]
    have e2 := L.2.2.1 (fun _ => 1) (r a) (α a) (h a (Finset.mem_insert_self a S))
    rw [wInt_one, wInt_one] at e2
    rw [e2]

end Manifold

theorem pullback_evalF {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f) {ι : Type} (w : ι → A.Pt → Ev n)
    (w' : ι → A'.Pt → Ev n') (hw : ∀ i, A.pullback A' f (fld A (w i)) = fld A' (w' i)) (P : MvPolynomial ι ℝ) :
    A.pullback A' f (evalF A w P) = evalF A' w' P := by
  have F := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf)
  induction P using MvPolynomial.induction_on with
  | C r => rw [evalF_C, evalF_C, (F.2 _ 1 1).2.2.1, F.1]
  | add P Q hP hQ => rw [evalF_add, evalF_add, (F.2 1 _ _).1, hP, hQ]
  | mul_X P i hP => rw [evalF_mul, evalF_mul, evalF_X, evalF_X, (F.2 1 _ _).2.1, hP, hw]

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem expand_line {R : Type} [CommRing R] [Algebra ℂ R] (ω θ c V : R) (hω : ω * ω = 0) (M : ℕ) :
    ω * (θ * (c - θ)) ^ M * V = ∑ j ∈ Finset.range (M + 1),
      (((-1) ^ j * (M.choose j : ℝ) : ℝ) : ℂ) • (ω * (θ + ω) ^ (M + j) * (c ^ (M - j) * V)) := by
  have hp : ∀ N : ℕ, ω * (θ + ω) ^ N = ω * θ ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_add]
      have e2 : ω * θ ^ N * ω = θ ^ N * (ω * ω) := by ring
      rw [e2, hω]
      ring
  have e : c - θ = -θ + c := by ring
  rw [mul_pow, e, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hp, Algebra.smul_def]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast,
    map_mul, map_pow, map_neg, map_one, map_natCast, neg_pow θ]
  ring

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem evalF_sum_C_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι κ : Type} (w : ι → A.Pt → Ev n)
    (S : Finset κ) (r : κ → ℝ) (P : κ → MvPolynomial ι ℝ) :
    evalF A w (∑ a ∈ S, C (r a) * P a) = ∑ a ∈ S, ((r a : ℝ) : ℂ) • evalF A w (P a) := by
  rw [evalF_eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, aeval_C, map_mul, evalF_eq, IsScalarTower.algebraMap_apply ℝ ℂ (A.Pt → Ev n), AlgHom.commutes,
    ← Algebra.smul_def]
  rfl

theorem downP_expand {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) :
    downP s m W = ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), C ((-1) ^ j * ((m i).choose j : ℝ) / ((m i : ℝ) + j + 1)) *
      (aeval ![X 1 + X 2, X 3] (hs (m i + j)) * ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i))) := by
  unfold downP
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← GlobalTheory.T.alternating_binomial_sum_eq_polynomial (m i)]
  simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X, Finset.sum_mul, MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.cons_val_zero]
  ring

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem fibre_integral_eq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (downP s m W)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ ι s m W
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hB.isProjOver
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  have I5B := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have I5Y := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have FB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have FY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have hol := (I5B.2.2 Y p (d + 1) hY π w).1
  set x : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx
  set ω := omF hY σ (h.pull π w) fl with hω
  set f4 := fam4 hB σ H flB A with hf4
  set g4 : Fin 4 → (hY.atlas σ).Pt → Ev (d + 1) := ![x 2, x 3, x 4, c2F hY σ (h.pull π w) fl] with hg4
  set φ : ι → ℕ → (hB.atlas σ).Fld := fun i j =>
    evalF (hB.atlas σ) f4 ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i)) with hφ
  set T : ι → ℕ → (hY.atlas σ).Fld := fun i j =>
    fld _ ω * (fld _ (x 0) + fld _ ω) ^ (m i + j) * pullF hB hY σ π w (φ i j) with hT
  set U : ι → ℕ → (hB.atlas σ).Fld := fun i j =>
    evalF (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m i + j))) * φ i j with hU
  set cf : ι → ℕ → ℝ := fun i j => (-1) ^ j * ((m i).choose j : ℝ) with hcf

  have hpull4 : ∀ i, (hB.atlas σ).pullback (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) (fld _ (f4 i)) = fld _ (g4 i) := by
    intro i
    fin_cases i
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 A).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 (VMetric.grLB flB 0 H)).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 (VMetric.grLB flB 1 H)).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.2 E h H flB fl).1.symm

  have hf4F : ∀ i, (hB.atlas σ).IsForm (fld _ (f4 i)) := by
    intro i
    fin_cases i
    · exact (I5B.1 A A).1.1
    · exact (I5B.1 (VMetric.grLB flB 0 H) A).1.1
    · exact (I5B.1 (VMetric.grLB flB 1 H) A).1.1
    · exact (I5B.2.1 E h H flB flB).2.1.1
  have hevB : ∀ P : MvPolynomial (Fin 4) ℝ, (hB.atlas σ).IsForm (evalF (hB.atlas σ) f4 P) :=
    fun P => (FB.2.2.2.1 _ f4 P hf4F).1
  have hφF : ∀ i j, (hB.atlas σ).IsForm (φ i j) := fun i j => hevB _
  have hUF : ∀ i j, (hB.atlas σ).IsForm (U i j) := fun i j => (FB.2.1 1 _ _ (hevB _) (hφF i j)).2.1
  have hωF : (hY.atlas σ).IsForm (fld _ ω) := (I5Y.2.1 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hθF : (hY.atlas σ).IsForm (fld _ (x 0)) := (I5Y.1 _ (fam5 π w H flB fl A 0)).1.1
  have hωω : ω * ω = 0 := (I5Y.2.1 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1
  have hTF : ∀ i j, (hY.atlas σ).IsForm (T i j) := by
    intro i j
    have hpF := (((FB.2.2.2.2 _ _ _ _ hol).2 1 (φ i j) (φ i j)).2.2.2 (hφF i j)).1
    exact (FY.2.1 1 _ _ (FY.2.1 1 _ _ hωF (isForm_pow _ (FY.2.1 1 _ _ hθF hωF).1 _)).2.1 hpF).2.1

  have hpT : ∀ i j, pullF hB hY σ π w (φ i j) =
      fldA _ ((x 3 + x 4) ^ (m i - j) * aeval ![x 2, x 3, x 4] (W i)) := by
    intro i j
    refine (pullback_evalF _ _ _ hol f4 g4 hpull4 ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i))).trans ?_
    rw [evalF_eq]
    congr 1
    simp only [map_mul, map_pow, map_add, aeval_X]
    rw [aeval_aeval']
    have e : (fun t : Fin 3 => aeval g4 ((![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 4) ℝ) t)) =
        ![x 2, x 3, x 4] := by
      funext t; fin_cases t <;> simp [g4]
    rw [e]
    rfl
  have hT' : ∀ i j, T i j =
      fldA _ (ω * (x 0 + ω) ^ (m i + j) * ((x 3 + x 4) ^ (m i - j) * aeval ![x 2, x 3, x 4] (W i))) := by
    intro i j
    simp only [hT, hpT, fld_eq, map_mul, map_pow, map_add]
  have hup : aeval x (upperParabolic s m W) = ∑ i ∈ s, (x 0 * (x 3 + x 4 - x 0)) ^ m i * aeval ![x 2, x 3, x 4] (W i) := by
    simp only [upperParabolic, map_sum, map_mul, map_pow, map_add, map_sub, aeval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_aeval']
    have e : (fun t : Fin 3 => aeval x ((![X 2, X 3, X 4] : Fin 3 → MvPolynomial (Fin 5) ℝ) t)) =
        ![x 2, x 3, x 4] := by
      funext t; fin_cases t <;> simp
    rw [e]
  have hY1 : fld _ ω * evalF _ x (upperParabolic s m W) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), ((cf i j : ℝ) : ℂ) • T i j := by
    rw [evalF_eq, fld_eq, ← map_mul, hup, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    refine (congrArg (fldA (hY.atlas σ)) (expand_line ω (x 0) (x 3 + x 4) (aeval ![x 2, x 3, x 4] (W i)) hωω (m i))).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hT']
  have hIY : (hY.atlas σ).integral (fld _ ω * evalF _ x (upperParabolic s m W)) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), cf i j * (hY.atlas σ).integral (T i j) := by
    rw [hY1, Finset.sum_sigma', Finset.sum_sigma']
    exact (integral_sum_smul (hY.atlas σ) (s.sigma fun i => Finset.range (m i + 1)) (fun a => cf a.1 a.2)
      (fun a => T a.1 a.2) fun a _ => hTF a.1 a.2).2

  have hB1 : evalF _ f4 (downP s m W) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), ((cf i j / ((m i : ℝ) + j + 1) : ℝ) : ℂ) • U i j := by
    rw [downP_expand, Finset.sum_sigma', Finset.sum_sigma', evalF_sum_C_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [evalF_mul]
  have hIB : (hB.atlas σ).integral (evalF _ f4 (downP s m W)) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), cf i j / ((m i : ℝ) + j + 1) * (hB.atlas σ).integral (U i j) := by
    rw [hB1, Finset.sum_sigma', Finset.sum_sigma']
    exact (integral_sum_smul (hB.atlas σ) (s.sigma fun i => Finset.range (m i + 1))
      (fun a => cf a.1 a.2 / ((m a.1 : ℝ) + a.2 + 1)) (fun a => U a.1 a.2) fun a _ => hUF a.1 a.2).2
  have hTU : ∀ i j, (hY.atlas σ).integral (T i j) = 1 / (((m i + j : ℕ) : ℝ) + 1) * (hB.atlas σ).integral (U i j) :=
    fun i j => (GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ (φ i j) (hφF i j) (m i + j)).2
  rw [hIY, hIB]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hTU]
  push_cast
  ring

end GlobalTheory.LineForm.ChernFibre
end
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_functional_chern_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    IsGeoFun L D Ψ → ∀ G : MvPolynomial ι ℝ, G.IsHomogeneous D →
      Ψ G = ∑ᶠ σ : k →+* ℂ, (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  first | exact @GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | exact GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | (intros; apply GlobalTheory.LineForm.GeoInt.geoFun_eq_integral <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.LogSinChern

open GlobalTheory.CxForm in

theorem isRegVar_of_isFlagBundle {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}
    (hB : IsRegVar q d) (hp : IsArithVar p (d + 1)) {π : Y ⟶ B} {E : B.Modules} (hE : GlobalTheory.VB.IsVB E 2)
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl)) : IsRegVar p (d + 1) := by
  have hπ := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π Unit (fun _ => E) (fun _ => 2) (fun _ => fl) (fun _ => hE) hfl
  have : Smooth π := @SmoothOfRelativeDimension.smooth _ _ _ π hπ
  have := hB.toIsArithVar.isLocallyNoetherian
  refine ⟨hp, fun y => ?_⟩
  have := GlobalTheory.ThetaExtend.isRegularRing_stalk hB.regular π y
  exact .of_isRegularRing_of_isLocalRing _

open GlobalTheory.LineForm GlobalTheory.CxForm in

theorem archInt_logSin_eq_chernNumber : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2) →
    ∀ (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ), (X 4 - X 0) * F = onLine d a b - onBase d a b →
    ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
      -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr = Ψ (G (d + 1) a b) := by
  intro _
  obtain ⟨R, hR⟩ := GlobalTheory.CovTest.SwapLine.exists_swap_coefficients
  refine ⟨fun D a b => Nat.casesOn D 0 fun d =>
    C (1 / 2 : ℝ) * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (R d a b)), ?_, ?_⟩
  · intro D a b
    cases D with
    | zero => exact isHomogeneous_zero _ _ _
    | succ d => exact (hR d a b).2.2.2
  intro k _ B Y _ _ q p d hq hp hreg π w E h H flB fl hfb A Ψ hΨ r hr hv a b F hF s c hc
  have hB : IsRegVar q d := ⟨hq, hreg⟩
  have hY : IsRegVar p (d + 1) := isRegVar_of_isFlagBundle hB hp h.isVB hfb
  choose v hv hv' using hv
  obtain ⟨h1, h2, h3, h4⟩ := hR d a b
  rw [GlobalTheory.T.arch_intersection_combination_log_norm k Y p (d + 1) hY (Fin 5) _ _ r hr (fun σ y => Real.log (1 - v σ y) / 2)
    (fun σ y hy => (hv' σ y hy).2) s c, ← hc, h1 F hF]
  erw [GlobalTheory.T.geometric_functional_chern_integral k Y p (d + 1) hY (Fin 3) _ Ψ hΨ _ h4]
  rw [← finsum_neg_distrib]
  refine finsum_congr fun σ => ?_
  rw [GlobalTheory.T.flag_bundle_chern_integral_pull_first k B Y q p d hB hY π w E h H flB fl hfb A σ (v σ) (hv σ) _ h2,
    GlobalTheory.T.flag_bundle_chern_integral_pull_second k B Y q p d hB hY π w E h H flB fl hfb A σ _ ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.1 E h H flB flB).1.1,
    GlobalTheory.LineForm.ChernFibre.fibre_integral_eq k B Y q p d hB hY π w E h H flB fl hfb A σ,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k B q d hB E h H flB A σ _ _ h3,
    GlobalTheory.LineGysin.gysin k B Y q p d hB hY π w E h H flB fl hfb A σ]
  ring

end GlobalTheory.LogSinChern
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_height_compare : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2) →
    ∀ (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ), (X 4 - X 0) * F = onLine d a b - onBase d a b →
    ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
      -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr = Ψ (G (d + 1) a b) := by
  atlas_forward_decl GlobalTheory.LogSinChern.archInt_logSin_eq_chernNumber
end
