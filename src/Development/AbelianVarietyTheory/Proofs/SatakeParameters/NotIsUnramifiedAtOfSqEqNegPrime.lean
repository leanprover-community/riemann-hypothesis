module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotSqMulUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
