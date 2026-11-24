module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem first_type_prime_large_of_record (D : D7) : StandardLattice.GBig D := by
  refine ⟨0, ?_⟩
  have hc := D.ntypes.g_cond 0
  have hg := (D.host.g_prime 0).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g 0 := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have hQ : 1 ≤ D.host.QS := D.host.QS_pos
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

end GlobalTheory
