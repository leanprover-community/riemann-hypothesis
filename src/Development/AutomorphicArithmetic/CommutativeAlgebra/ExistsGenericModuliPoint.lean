module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
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

@[expose] public section

namespace UpperTheory

open UpperTheory.Gal.Int.Geo

theorem exists_generic_moduli_point : GenEx := by
  intro A _ _ _ 𝔞 N hN
  have hN0 : (N : A) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun hmem => ?_, fun a t h => ?_⟩
  · have hdvd : 𝔞 ∣ Ideal.span {(N : A)} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    obtain ⟨𝔟, h𝔟⟩ := hdvd
    have hle : Ideal.span {(N : A)} ≤ 𝔟 := by
      rw [h𝔟]; exact Ideal.mul_le_right
    have hne : Ideal.span {(N : A)} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hN0
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    refine ⟨a, ?_⟩
    unfold IsGen
    rw [sup_comm, ha, mul_comm, ← h𝔟]
  · unfold IsGen at h ⊢
    have hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)}
        = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)}) := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]
    rw [hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]

end UpperTheory
