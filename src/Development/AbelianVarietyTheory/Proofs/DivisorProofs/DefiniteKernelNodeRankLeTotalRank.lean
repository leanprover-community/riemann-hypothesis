module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.DefRank

theorem rank_le_bigN : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node),
    DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  intro D T L sc G X hX
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hm := D.R.two_le_m
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := hX.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e, D.sp.X'_rank]
    show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · obtain ⟨hi, rfl⟩ := hX
    rw [(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]
    show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have := Nat.mul_le_mul_right (sLen D) hi
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · exact hX.elim
  · rw [(G.isV (X := .top j) hX (by simp)).rank]
    show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have h1 := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)
    have hs : sLen D - 1 + 1 = sLen D := by unfold sLen; omega
    have hn : nRk D = D.R.r + 1 := rfl
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
      conv_lhs => rw [← hs]
      ring
    have h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := h1
    omega

end GlobalTheory.DefRank
