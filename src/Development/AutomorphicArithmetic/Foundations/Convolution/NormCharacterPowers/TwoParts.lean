module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.twoParts :
    ClassChar → Count → NormCharPow → TwoParts := by
  classical
  intro hC hCount hN K M _ _ _ _ _ _ _ _ hp n π ι _ m P hn hm hι hW
  obtain ⟨η, hη⟩ := hC K M hp
  have h1 := hCount K M hp η hη n π π ι m P hn hm hW hW
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι from hι)
  have h2 : 1 < ((Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j)).card := by
    rw [h1, Finset.one_lt_card]
    refine ⟨(a, a), by simp, (b, b), by simp, fun h => hab (congrArg Prod.fst h)⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_ne h2 0
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨η ^ j, (hN K M hp η hη).2 j (Nat.pos_of_ne_zero hj0) hj.1, hj.2.symm⟩
