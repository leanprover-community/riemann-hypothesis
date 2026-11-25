module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem algHom_coe_eq_aeval {O T : Type} [CommRing O] [CommRing T] [Algebra O T]
    (ρ : PowerSeries O →ₐ[O] T) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    all_goals first
      | exact ρ.commutes a

theorem constantCoeff_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (x : PowerSeries S) (r : Polynomial O) :
    constantCoeff (Polynomial.aeval x r) = Polynomial.aeval (constantCoeff x) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1

theorem eq_of_X_mul_eq {S : Type} [CommRing S] {f g : PowerSeries S}
    (h : (X : PowerSeries S) * f = X * g) : f = g := by
  first
  | (ext n; simpa [PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff (n + 1)) h)

theorem rhoCompl : RhoComplStatement := by
  intro O LL S _ _ _ _ _ _ _ _ _ _ _ P hP ρ hunit hann
  have hmon : P.Monic := by first | exact hP.monic
  have hd := hP.isWeierstrassDivisorAt (maximalIdeal.isMaximal O).ne_top
  have hord : ((P : PowerSeries O).map (Ideal.Quotient.mk (maximalIdeal O))).order.toNat =
      P.natDegree :=
    (congrArg ENat.toNat (hP.coe_natDegree_eq_order_map (P : PowerSeries O) 1
      (by simp)
      (mul_one _).symm)).symm
  have key : ∀ a : PowerSeries O, (X : PowerSeries S) ∣ ρ a → (P : PowerSeries O) ∣ a := by
    intro a ha
    let q := hd.div a
    let r := hd.mod a
    have hdiv := hd.isWeierstrassDivisionAt_div_mod a
    have hr : r.degree < P.natDegree := by rw [← hord]; exact hdiv.degree_lt
    have he : a = (P : PowerSeries O) * q + r := hdiv.eq_mul_add
    obtain ⟨w, hw⟩ := hunit
    have hρa : ρ a = (w : PowerSeries S) * X * ρ q + Polynomial.aeval (ρ X) r := by
      rw [he, map_add (f := _), map_mul, hw, algHom_coe_eq_aeval]
    have h0 : constantCoeff (ρ a) = 0 := by
      obtain ⟨c, hc⟩ := ha
      rw [hc, map_mul, PowerSeries.constantCoeff_X, zero_mul]
    have hr0 : Polynomial.aeval (constantCoeff (ρ X)) r = 0 := by
      have h1 := congrArg constantCoeff hρa
      rw [h0, map_add (f := _), map_mul, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul, zero_add,
        constantCoeff_aeval] at h1
      exact h1.symm
    have hdvd : P.map (algebraMap O LL) ∣ r.map (algebraMap O LL) := by
      apply hann
      first | (rw [Polynomial.aeval_map_algebraMap]; exact hr0)
    have hmap0 : r.map (algebraMap O LL) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
      calc (r.map (algebraMap O LL)).degree ≤ r.degree := by
            first | exact Polynomial.degree_map_le
        _ < P.natDegree := hr
        _ = P.degree := (Polynomial.degree_eq_natDegree hmon.ne_zero).symm
        _ = (P.map (algebraMap O LL)).degree := (hmon.degree_map _).symm
    have hr' : r = 0 := by
      apply Polynomial.map_injective (algebraMap O LL) (IsFractionRing.injective O LL)
      rw [hmap0, Polynomial.map_zero]
    rw [hr', Polynomial.coe_zero, add_zero] at he
    exact ⟨q, he⟩
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := key a (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) ha)
    obtain ⟨w, hw⟩ := hunit
    rw [map_mul, hw] at ha
    obtain ⟨c, hc⟩ := ha
    have h2 : (w : PowerSeries S) * ρ b = X ^ k * c := by
      apply eq_of_X_mul_eq
      linear_combination hc
    have hb : (X : PowerSeries S) ^ k ∣ ρ b := by
      refine ⟨(↑w⁻¹ : PowerSeries S) * c, ?_⟩
      calc ρ b = (↑w⁻¹ : PowerSeries S) * ((w : PowerSeries S) * ρ b) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = (↑w⁻¹ : PowerSeries S) * (X ^ k * c) := by rw [h2]
        _ = X ^ k * ((↑w⁻¹ : PowerSeries S) * c) := by ring
    obtain ⟨d, hd⟩ := ih b hb
    exact ⟨d, by rw [hd]; ring⟩

end LevelStatements.Lv
