module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
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

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem fix_and_win_of_numAt (eps : ℝ) (C : FC) (Fm : FamP eps) (hS : Std C) (hO : Fm.cOut = C.cOut)
    (hN : ∀ x (i : Fm.Ix x), Nonempty (NumAt C (Fm.L x i))) : DC.PageFix Fm ∧ DC.PageWin Fm := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, sCt⟩, sCc, -, -, scw, sCYL, -, sCp, seP, scTO, -, sCe, -⟩ := hS
  simp only [FamP.cOut, FC.cOut, List.cons.injEq] at hO
  obtain ⟨oCt, oCc, -, -, -, ocw, oCYL, -, -, -, oCp, oeP, ocTO, -, oCe, -⟩ := hO
  refine ⟨⟨oCp.trans sCp, oeP.trans seP, ?_, ?_, oCe.trans sCe, oCc.trans sCc, ocw.trans scw, oCYL.trans sCYL,
    fun x hx i => ?_⟩, fun x hx i => ?_⟩
  · rw [ocTO, oeP, scTO, seP]; norm_num
  · rw [ocTO, oCt, scTO, sCt]; norm_num
  · obtain ⟨N⟩ := hN x i
    refine ⟨N.ccK_top, N.cloud1, N.g_le, N.pde_lt.1, N.pde_lt.2, N.logFiveDepth_eq, ?_, ?_⟩
    · have h := N.Lw_eq
      rw [Fm.L_x x i hx, Fm.L_eps x i, ← oCt] at h
      exact h
    · have h := (Fm.parT x hx i).TO_eq
      rw [Fm.parT_cTO, Fm.L_x x i hx] at h
      exact h
  · obtain ⟨N⟩ := hN x i
    have h := N.win
    rw [Fm.L_x x i hx, Fm.L_eps x i] at h
    exact h

end GlobalTheory.EX.DC
