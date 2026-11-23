module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
