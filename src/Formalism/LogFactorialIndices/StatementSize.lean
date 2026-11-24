module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
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

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def PhIncr : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 ≤ u ∨ 1 ≤ v) → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

end Formalism.LatticeIndexTer
