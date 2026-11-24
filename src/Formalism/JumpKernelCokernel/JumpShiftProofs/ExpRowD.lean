module

public import Formalism.JumpKernelCokernel.Statement
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
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

namespace Formalism.KernelCokernelLengths

theorem row_degree_exponent : ExpRowD := by
  intro ℓ hℓ h η S b a s₁ E e₂ hη hb ha hs hE he
  have key := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement ℓ hℓ h η S b a s₁ E e₂ hb ha hs hE he
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
  have hη' : (2 * (η : ℝ)) ≤ h := by exact_mod_cast hη
  have hc : 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hℓ2.le
    push_cast
    nlinarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  linarith

end Formalism.KernelCokernelLengths
