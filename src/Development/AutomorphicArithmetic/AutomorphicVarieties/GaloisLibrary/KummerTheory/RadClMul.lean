module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem finSupp {K : Type} [Field K] [NumberField K] {G : Type} [CommGroup G]
    (g : HeightOneSpectrum (𝓞 K) → G) (n : ℤ) (a : Kˣ) :
    Function.HasFiniteMulSupport fun v => g v ^ (ordv v a / n) := by
  refine ((clProd K).2.2.1 a).subset fun v hv => ?_
  intro h
  apply hv
  simp [h]

private theorem mk_radCl {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) (a : Kˣ) :
    (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / n) := by
  have h := (QuotientGroup.mk' (clSub S)).map_finprod (finSupp primeCl (n : ℤ) a)
  simpa [radCl] using h

private theorem mk_primeCl {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)

private theorem ordv_pow' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) :
    ordv v (b ^ n) = n * ordv v b := by
  induction n with
  | zero => simp [ordv_one]
  | succ m ih => rw [pow_succ, ordv_mul, ih]; push_cast; ring

theorem UpperTheory.V.Kum.radClMul :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → (∀ a ∈ SelK S n, ∀ b ∈ SelK S n, (QuotientGroup.mk (radCl n (a * b)) : ClS S) = QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b)) ∧
    (∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1) ∧ (∀ a b : Kˣ, radCl n (a * b ^ n) = radCl n a) := by
  intro K _ _ S n hn
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have h1 : ∀ x : Kˣ, radCl 1 x = 1 := (clProd K).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mk_radCl S n, mk_radCl S n, mk_radCl S n,
      ← finprod_mul_distrib (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)
        (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) b)]
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simp [mk_primeCl hv]
    · rw [ordv_mul, Int.add_ediv_of_dvd_right (hb v hv), zpow_add]
  · intro a ha
    have e := mk_radCl S 1 a
    rw [h1 a] at e
    simp only [Nat.cast_one, Int.ediv_one, QuotientGroup.mk_one] at e
    have key : ∀ v : HeightOneSpectrum (𝓞 K),
        ((QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / (n : ℤ))) ^ n =
          (QuotientGroup.mk (primeCl v) : ClS S) ^ ordv v a := by
      intro v
      by_cases hv : v ∈ S
      · simp [mk_primeCl hv]
      · rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (ha v hv)]
    rw [mk_radCl S n, finprod_pow (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a),
      finprod_congr key]
    exact e.symm
  · intro a b
    have e := h1 b
    simp only [radCl, Nat.cast_one, Int.ediv_one] at e
    have hb1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) => primeCl v ^ ordv v b := by
      have h := finSupp (primeCl (K := K)) 1 b
      simpa only [Int.ediv_one] using h
    simp only [radCl]
    rw [finprod_congr (fun v => show primeCl v ^ (ordv v (a * b ^ n) / (n : ℤ)) =
        primeCl v ^ (ordv v a / (n : ℤ)) * primeCl v ^ ordv v b by
          rw [ordv_mul, ordv_pow', Int.add_mul_ediv_left _ _ hn', zpow_add]),
      finprod_mul_distrib (finSupp primeCl (n : ℤ) a) hb1, e, mul_one]
