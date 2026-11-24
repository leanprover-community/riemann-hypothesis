module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.HC

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R) {p : ℕ}

theorem cls_splitK_or_small (hp : p.Prime) (h : p ≤ H.splitBound) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    H.cls p = .splitK ∨ p ∈ H.small := by
  by_cases hs : p ∈ H.small
  · exact Or.inr hs
  · have h2 : p ≠ 2 := fun e => hs (e ▸ H.two_mem_small)
    exact Or.inl ((primeClass_eq_splitK_iff H.toHostRaw).2 ⟨hs, hq, hd, H.split_small p hp h2 h⟩)

end Formalism.BasicNotions.Host
