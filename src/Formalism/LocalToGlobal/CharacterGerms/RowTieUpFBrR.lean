module

public import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
public import Formalism.LocalToGlobal.CharacterGerms.PlugUP
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

structure RingPk {C : Type} [Field C] (V : VF C) where
  vm : Valuation C NNReal
  tie : ValTie V vm
  int : vm.Integers V.RR
  pos : 0 < (vm (V.l : C) : ℝ)
  lt : (vm (V.l : C) : ℝ) < 1
  nonunit : ¬ IsUnit ((V.l : ℕ) : V.RR)
  cpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR
  loc : IsLocalRing V.RR
  alg : Algebra ℤ_[V.l] V.RR
  mm : ∀ x : V.RR, V.MM (x : C) → x ∈ IsLocalRing.maximalIdeal V.RR

def RingPkSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → Nonempty (RingPk V)

end UpFBr

end Formalism.L2.FormalSeriesBounds
