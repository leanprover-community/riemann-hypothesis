module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
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
import Mathlib.Tactic.Linter.Style
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal

section Abs

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

theorem inv_invariant_of_bi_invariant [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [SigmaFinite μ]
    (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) : μ.IsInvInvariant := by
  open scoped Pointwise in
    have hUo : IsOpen {h : G | f 1 / 2 < f h} := isOpen_lt continuous_const hf
    have h1U : (1 : G) ∈ {h : G | f 1 / 2 < f h} := by
      show f 1 / 2 < f 1
      linarith
    have hUfin : μ {h : G | f 1 / 2 < f h} < ⊤ := by
      refine lt_of_le_of_lt (measure_mono fun h hh => ?_) (hi.measure_norm_ge_lt_top (half_pos h1))
      have hh' : f 1 / 2 < f h := hh
      show f 1 / 2 ≤ ‖f h‖
      rw [Real.norm_eq_abs]
      exact hh'.le.trans (le_abs_self _)
    have hso : IsOpen ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) := hUo.inter hUo.inv
    have hs1 : (1 : G) ∈ {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ :=
      ⟨h1U, by rw [Set.mem_inv, inv_one]; exact h1U⟩
    have hsinv : ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹)⁻¹ =
        {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ := by
      rw [Set.inter_inv, inv_inv, Set.inter_comm]
    have hs0 : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ 0 :=
      hso.measure_ne_zero μ ⟨1, hs1⟩
    have hstop : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUfin).ne
    have key := measure_eq_div_smul μ.inv μ hs0 hstop
    rw [Measure.inv_apply, hsinv, ENNReal.div_self hs0 hstop, one_smul] at key
    exact ⟨key⟩

open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)

variable {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]

end Abs

end Formalism.MainNotions.BridgeLemma

end
