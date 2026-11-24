module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_two (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hn : Algebra.norm ℤ ((p : 𝓞 K)) = (p : ℤ) ^ 2 := by
    rw [show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, h2]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast]

theorem ne_bot_of_absNorm {P : Ideal (𝓞 K)} {n : ℕ} (hP : Ideal.absNorm P = n) (hn : n ≠ 0) :
    P ≠ ⊥ := by
  rintro rfl
  rw [Ideal.absNorm_bot] at hP
  exact hn hP.symm

end PI.ClassNumImQ.ZetaNonvanishing₂
