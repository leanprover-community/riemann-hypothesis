module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem exists_pow_mul_pow_mul_pow_dvd_prod_pow {B : Type} [CommRing B] {ι : Type} (t x y : B)
    (ξ : ι → B) (hξ : ∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) (u : ι → ℕ) (s : Finset ι) :
    ∃ a b c : ℕ, a + b + c = ∑ q ∈ s, u q ∧ t ^ a * x ^ b * y ^ c ∣ ∏ q ∈ s, ξ q ^ u q := by
  classical
  induction s using Finset.induction_on
  case empty => exact ⟨0, 0, 0, by simp, by simp⟩
  case insert q s hq ih =>
    obtain ⟨a, b, c, habc, hd⟩ := ih
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    rcases hξ q with ⟨r, hr⟩ | hx | hy
    · refine ⟨u q + a, b, c, by omega, ?_⟩
      have h := mul_dvd_mul (dvd_mul_right (t ^ u q) (r ^ u q)) hd
      rw [hr, mul_pow]
      convert h using 1
      ring
    · refine ⟨a, u q + b, c, by omega, ?_⟩
      have h := mul_dvd_mul_left (x ^ u q) hd
      rw [hx]
      convert h using 1
      ring
    · refine ⟨a, b, u q + c, by omega, ?_⟩
      have h := mul_dvd_mul_left (y ^ u q) hd
      rw [hy]
      convert h using 1
      ring

theorem aeval_eq_zero_of_low_coeff_of_three_nilpotent :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ)
      (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 →
      (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) →
      (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t x y K m ξ F ht hx hy hξ hF
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hu : u.degree < K + m
  · rw [hF u hu, zero_mul]
  · obtain ⟨a, b, c, habc, hd⟩ := exists_pow_mul_pow_mul_pow_dvd_prod_pow t x y ξ hξ u u.support
    have hdeg : u.degree = ∑ q ∈ u.support, u q := rfl
    have hzero : t ^ a * x ^ b * y ^ c = 0 := by
      by_cases hc : m ≤ c
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
        rw [pow_add, hy]
        simp
      · by_cases hb : 2 ≤ b
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [pow_add, pow_two, hx]
          simp
        · have hK : K ≤ a := by omega
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          rw [pow_add, ht]
          simp
    rw [hzero, zero_dvd_iff] at hd
    rw [Finsupp.prod]
    simp only [hd, mul_zero]

end GlobalTheory.NewPrime
