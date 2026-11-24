module

public import Formalism.LocalRingCardinality.Params
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

namespace Formalism.BasicNotions.Examples₂

noncomputable def R0 : Formalism.BasicNotions.Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 2
  t := 15
  k_even := ⟨4, rfl⟩
  m_even := ⟨1, rfl⟩
  t_odd := ⟨7, rfl⟩
  two_le_m := le_refl _
  m_add_three_le_k := by norm_num
  rank_add_five_le := by norm_num
  three_m_lt_t := by norm_num
  m_le_f := (by norm_num : 2 ≤ 2 * 2 ^ 2)
  f_le_k := (by norm_num : 2 * 2 ^ 2 ≤ 8)
  m_sq_le_N := by norm_num

theorem exampleRanks_baseRank : R0.n0 = 4 := by
  show (Formalism.HC.frameCyc 2 1).n0 = 4
  rw [Formalism.HC.frameCyclic_order]
  exact ZMod.addOrderOf_one _
theorem exampleRanks_o : R0.o = 1 := by
  show R0.toFrame.ord / R0.toFrame.n0 = 1
  have h1 : R0.toFrame.n0 = 4 := exampleRanks_baseRank
  have h2 : R0.toFrame.ord = 4 := rfl
  rw [h1, h2]
theorem exampleRanks_h_injective : Function.Injective R0.h :=
  Formalism.HC.frameCyc_h_injective 2 1

end Formalism.BasicNotions.Examples₂
