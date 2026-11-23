module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMoment

theorem prod_ratio {r : ℕ} (l : Fin (r + 1) → ℝ) (hl : ∀ a, 0 < l a) (a : Fin (r + 1)) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin r => a.val ≤ c.val), l c.succ / l c.castSucc
      = l (Fin.last r) / l a := by
  induction a using Fin.reverseInduction with
  | last =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.last r).val ≤ c.val) = ∅ := by
      ext c
      have := c.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, Finset.notMem_empty, iff_false]
      omega
    rw [this, Finset.prod_empty, div_self (hl _).ne']
  | cast i ih =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.castSucc i).val ≤ c.val)
        = insert i (Finset.univ.filter (fun c : Fin r => (Fin.succ i).val ≤ c.val)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
        Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [this, Finset.prod_insert (by simp), ih]
    have h1 := (hl i.succ).ne'
    have h2 := (hl i.castSucc).ne'
    field_simp

end GlobalTheory.InvLenMoment
