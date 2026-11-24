module

public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace Formalism.BasicNotions

def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)

def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0

structure JetLoc where

  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l

  d : ℕ
  [hd : NeZero d]
  d_even : Even d
  two_le_d : 2 ≤ d

  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc.hl JetLoc.hd

structure JetLoc1 where
  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l
  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc1.hl

structure ThetaJet (R : Ranks) (host : Host R) : Type 1 where
  Sit : Type
  loc : Sit → JetLoc

  l_inert : ∀ i, host.cls (loc i).l = .signal ∨ host.cls (loc i).l = .inertClass
  jOf : Sit → ℕ
  j_mem : ∀ i, 1 ≤ jOf i ∧ jOf i ≤ R.m
  N0_eq : ∀ i, (loc i).N0 = R.N (jOf i - 1)
  N1_eq_exponentN1 : ∀ i, (loc i).N1 = R.N (jOf i)
  Sit1 : Type
  loc1 : Sit1 → JetLoc1
  l_inert1 : ∀ i, host.cls (loc1 i).l = .inertClass ∧ ¬ HNeZero host (loc1 i).l
  j1Of : Sit1 → ℕ
  firstJetIndex_mem_range : ∀ i, 1 ≤ j1Of i ∧ j1Of i ≤ R.m
  firstJet_lowerRank_eq : ∀ i, (loc1 i).N0 = R.N (j1Of i - 1)
  firstJet_upperRank_eq : ∀ i, (loc1 i).N1 = R.N (j1Of i)

end Formalism.BasicNotions

end
