module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open ValuativeRel

noncomputable section

namespace GlobalTheory.DZero.PsiM

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (uniformizer k) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {k}

theorem ord_eq_one {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : SmGL.ord k ϖ = 1 := by
  rw [SmGL.ord, hϖ, valueGroupIso_uniformizer, WithZero.log_exp]; rfl

end GlobalTheory.DZero.PsiM
