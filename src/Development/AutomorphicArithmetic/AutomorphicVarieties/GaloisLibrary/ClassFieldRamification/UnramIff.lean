module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.unramIff :
    (∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ), p.Prime → (UnramAt L p ↔ ∀ w : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ w.asIdeal → w.asIdeal.inertia Gal(L/ℚ) = ⊥)) ∧ (∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L)) ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime → UnramAt L p → UnramAt K p := by
  have h2 : ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
      (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L) := by
    intro L _ _ p hp
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    unfold UnramAt
    refine forall_congr' fun P => forall_congr' fun hP => ?_
    haveI := hP
    rw [Int.cast_natCast, Ideal.ramificationIdx_eq_one_iff]
  refine ⟨?_, h2, ?_⟩
  · intro L _ _ _ p hp
    unfold UnramAt
    constructor
    · intro h w hw
      haveI := w.isPrime
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
      exact h w.asIdeal w.isPrime hw
    · intro h P hP hpP
      haveI := hP
      have hne : P ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hw := h ⟨P, hP, hne⟩ hpP
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hw
      exact hw
  · intro K L _ _ _ _ _ p hp hL
    exact (h2 K p hp).2 fun hd => (h2 L p hp).1 hL (hd.trans (NumberField.discr_dvd_discr K L))
