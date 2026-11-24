module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def coarseUnit (P n : ℕ) : ℚ :=
  ((P * n).factorial : ℚ) / (((P.factorial : ℚ) ^ n) * (n.factorial : ℚ))

def CoarseUnitProd : Prop :=
  ∀ P n : ℕ, 1 ≤ P →
    coarseUnit P n = ∏ i ∈ range n, ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * i / y)

def HarmonicVal : Prop :=
  ∀ p t s : ℕ, p.Prime →
    (s : ℤ) ≤ padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s)

def PowerSumPoly : Prop :=
  ∀ s : ℕ, ∃ f : Polynomial ℚ, f.natDegree = s + 1 ∧
    ∀ n : ℕ, f.eval (n : ℚ) = ∑ i ∈ range n, (i : ℚ) ^ s

def rhoP (p : ℝ) : ℝ := 1 / (p ^ 2 - 1)

def gamP (p : ℝ) : ℝ := p * rhoP p

def GammaIdentity : Prop :=
  ∀ p : ℝ, 1 < p →
    HasSum (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) (gamP p) ∧ gamP p = 1 / (p - 1) - rhoP p

def gainG {n : ℕ} (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de : ℝ) : ℝ :=
  gamP p * ∑ s ∈ TT, al s -
    ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) - de

def excessGain {n : ℕ} (p : ℝ) (TT : Finset (ZMod n)) (D : ZMod n → Finset ℕ) (al cap : ZMod n → ℝ)
    (de : ℝ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ,
    (if 2 * e + 1 ∈ D s then 0 else max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)
    - de

end Formalism.GrowthSums
