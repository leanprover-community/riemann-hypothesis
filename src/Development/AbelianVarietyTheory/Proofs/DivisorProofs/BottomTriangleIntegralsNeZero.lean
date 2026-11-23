module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NonVanBottom

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  omega

theorem exists_ne_zero_of_integral {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ}
    (h : (∫ y in S, ‖f y‖ ^ 2 ∂ν) ≠ 0) : ∃ y, f y ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (by simp [hc])

theorem exists_ne_zero_of_norm_formula {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ} {c : ℂ}
    {Λ : ℂ → ℂ} {a b : ℤ} (hc : c ≠ 0) (hΛ : ∀ s : ℤ, a ≤ s → s ≤ b → Λ s ≠ 0)
    (h : ((∫ y in S, ‖f y‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc a b, Λ s) : ∃ y, f y ≠ 0 := by
  refine exists_ne_zero_of_integral (ν := ν) (S := S) fun h0 => ?_
  have hp : ∏ s ∈ Icc a b, Λ s ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => hΛ s (mem_Icc.1 hs).1 (mem_Icc.1 hs).2
  rw [h0, Complex.ofReal_zero] at h
  exact mul_ne_zero hc hp h.symm

end GlobalTheory.NonVanBottom

end
