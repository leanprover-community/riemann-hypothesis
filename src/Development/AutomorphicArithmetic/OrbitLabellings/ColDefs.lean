module

public import Formalism.GaussJetBounds.GenLogInverse
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

noncomputable section

open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds

namespace UpperTheory.G2

structure IsPos {Lt : Type} (i : ℕ) (pos : Lt → ℕ → Lt) : Prop where
  zero : ∀ z, pos z 0 = z
  add : ∀ z a b, pos (pos z a) b = pos z (a + b)
  period : ∀ z, pos z i = z

section Series

variable {K : Type} {Lt β : Type}

def logS [Field K] [DecidableEq Lt] [DecidableEq β] (l i : ℕ) (pos : Lt → ℕ → Lt) (v : Lt × β) : MvPowerSeries (Lt × β) K :=
  genLog l (fun y : Lt × β => (pos y.1 (2 * (i - 1)), y.2)) v

def beS [Field K] [Fintype β] (i : ℕ) (pos : Lt → ℕ → Lt) (R : Finset Lt) (sg : Lt → K)
    (be : Lt → MvPowerSeries (ZMod (2 * i)) K) : MvPowerSeries (Lt × β) K :=
  ∑ r ∈ R, (sg r / 2) • ∑ b : β,
    MvPowerSeries.subst (fun s : ZMod (2 * i) => (MvPowerSeries.X (pos r s.val, b) : MvPowerSeries (Lt × β) K)) (be r)

def ShapeS [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) (pos : Lt → ℕ → Lt)
    (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K) (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ U : MvPowerSeries (Lt × β) K, Integral U ∧
    MvPowerSeries.subst (fun v : Lt × β => MvPowerSeries.C ep * logS (K := K) l i pos v) Th =
      U * MvPowerSeries.subst (logS (K := K) (β := β) l i pos) (mvExp (beS i pos R sg be))

def HasThetaProductForm [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt)
    (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ (K0 : Subfield K) (ζ : K) (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K),
    Unram l K0 ∧ IsPrimitiveRoot ζ (l ^ (2 * i) - 1) ∧ ‖ep‖ = 1 ∧ (∀ r ∈ R, sg r = 1 ∨ sg r = -1) ∧
      (∀ r ∈ R, BHyp l (2 * i) K0 ζ (be r)) ∧ ShapeS l i pos R ep sg be Th

def linS [Field K] {K0 : Type} [Field K0] (j : K0 →+* K) (σ : K0 →+* K0) (i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt) (c : K0) (r : Lt)
    (b : β) : MvPowerSeries (Lt × β) K :=
  ∑ s : ZMod (2 * i), if s.val % 2 = 0 then MvPowerSeries.C (j (σ^[s.val] c)) * MvPowerSeries.X (pos r s.val, b) else 0

end Series

def IsRadii {Lt : Type} (l : ℕ) (pos : Lt → ℕ → Lt) (sig : Lt → ℝ) : Prop :=
  (∀ z, 0 ≤ sig z) ∧ ∀ z, ∀ e : ℕ, Odd e → 1 ≤ (l : ℝ) ^ e * sig z + sig (pos z e)

end UpperTheory.G2

end
