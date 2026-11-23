module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma unit_add_nonunit {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (hx : IsUnit x) (hy : ¬ IsUnit y) : IsUnit (x + y) := by
  by_contra h
  have hy' : ¬ IsUnit (-y) := by rwa [IsUnit.neg_iff]
  have := IsLocalRing.nonunits_add h hy'
  rw [add_neg_cancel_right] at this
  exact this hx

private lemma natCast_not_isUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∈ v.asIdeal) :
    ¬ IsUnit (q : v.adicCompletionIntegers F) := by
  intro hu
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
  have h1 : v.intValuation (q : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hq
  have h2 : ((q : v.adicCompletionIntegers F) : v.adicCompletion F) = (q : v.adicCompletion F) := by
    simp
  have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  have h4 := HeightOneSpectrum.valuation_of_algebraMap (K := F) v (q : 𝓞 F)
  push_cast at h3 h4
  rw [h2, h3, h4] at hu
  exact (ne_of_lt h1) hu

theorem UpperTheory.Gal.G1.pLocRoot :
    HenselV → LocRoot := by
  intro hH F _ _ v tr nm q hqp hqv hdisc hr
  obtain ⟨r, k, hk⟩ := hr
  have hq : ¬ IsUnit (q : v.adicCompletionIntegers F) := natCast_not_isUnit F v q hqv
  have hqi : Irreducible (q : ℤ) := (Nat.prime_iff_prime_int.mp hqp).irreducible
  have hint : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → IsUnit (n : v.adicCompletionIntegers F) := by
    intro n hn
    obtain ⟨a, b, hab⟩ := (hqi.coprime_iff_not_dvd).2 hn
    have hab' : ((a : v.adicCompletionIntegers F)) * (q : v.adicCompletionIntegers F)
        + (b : v.adicCompletionIntegers F) * (n : v.adicCompletionIntegers F) = 1 := by
      have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hab
      push_cast at this
      exact this
    have hnu : ¬ IsUnit (-((a : v.adicCompletionIntegers F) * (q : v.adicCompletionIntegers F))) := by
      rw [IsUnit.neg_iff]
      exact fun h => hq (isUnit_of_mul_isUnit_right h)
    have hbn := unit_add_nonunit isUnit_one hnu
    rw [← hab', add_neg_cancel_comm] at hbn
    exact isUnit_of_mul_isUnit_right hbn
  have hder : ¬ (q : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hdisc
    have e : tr ^ 2 - 4 * nm = (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) := by ring
    rw [e, hk]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  set f : Polynomial (v.adicCompletionIntegers F) :=
    Polynomial.X ^ 2 - Polynomial.C (tr : v.adicCompletionIntegers F) * Polynomial.X
      + Polynomial.C (nm : v.adicCompletionIntegers F) with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hev : ∀ x, f.eval x = x ^ 2 - (tr : v.adicCompletionIntegers F) * x + nm := by
    intro x
    simp [hf]
  have hdev : ∀ x, (Polynomial.derivative f).eval x = 2 * x - (tr : v.adicCompletionIntegers F) := by
    intro x
    simp only [hf, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    push_cast
    ring
  have h0 : ¬ IsUnit (f.eval (r : v.adicCompletionIntegers F)) := by
    rw [hev]
    have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hk
    push_cast at this
    rw [this]
    exact fun h => hq (isUnit_of_mul_isUnit_left h)
  have h1 : IsUnit ((Polynomial.derivative f).eval (r : v.adicCompletionIntegers F)) := by
    rw [hdev]
    have := hint _ hder
    push_cast at this
    exact this
  obtain ⟨ρ, hρ, hρr⟩ := hH F v f r hmon h0 h1
  refine ⟨ρ, ?_, ?_⟩
  · rw [hev] at hρ
    exact hρ
  · have h2 : ¬ IsUnit (2 * (ρ - (r : v.adicCompletionIntegers F))) :=
      fun h => hρr (isUnit_of_mul_isUnit_right h)
    have h3 := unit_add_nonunit ((hdev _) ▸ h1) h2
    have e : 2 * (r : v.adicCompletionIntegers F) - tr + 2 * (ρ - r) = 2 * ρ - tr := by ring
    rw [e] at h3
    exact h3
