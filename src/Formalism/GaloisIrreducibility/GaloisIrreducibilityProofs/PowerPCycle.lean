module

public import Formalism.GaloisIrreducibility.Statement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.GaloisIrreducibility

theorem power_of_p_cycle : PowerPCycle := by
  intro α _ _ σ p hp hmem hcard
  have hdvd : p ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hmem
  have hpos : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  refine ⟨orderOf σ / p, ?_⟩
  have hord : orderOf (σ ^ (orderOf σ / p)) = p := orderOf_pow_orderOf_div hpos hdvd
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ ^ (orderOf σ / p)) (by rw [hord]; exact hp)
  rw [hord] at hn
  have hsum : (σ ^ (orderOf σ / p)).support.card = (n + 1) * p := by
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul]
  have hle : (σ ^ (orderOf σ / p)).support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    have h3 : 2 * p ≤ Fintype.card α := h2.trans (hsum ▸ hle)
    omega
  subst hn0
  refine ⟨?_, by rw [hsum]; ring⟩
  rw [← Equiv.Perm.card_cycleType_eq_one, hn]
  simp

end Formalism.GaloisIrreducibility
