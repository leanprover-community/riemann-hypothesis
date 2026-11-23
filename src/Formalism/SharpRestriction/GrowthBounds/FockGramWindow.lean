module

public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.InitialPointNumericBound
public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.WinLvl
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthBasisLat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiagRank
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatMin
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.FirstCoefficientLeDiv
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfMinimalVector
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem restWinE_proved (D : Formalism.BasicNotions.D7) : RestWinE D := by
  intro Cc _
  refine ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨2, two_pos, fun CYb Cde Ck CD Cb a1 _ _ a4 a5 => ?_⟩⟩⟩
  intro Ckap Cs CM hCM X _ hH
  have hS : SegFacts C0 CE1 CE2 X := segFacts a1 (by linarith) (by linarith) (by linarith) (by linarith) hH
  have hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ) := by
    obtain ⟨h0, -⟩ := hH
    obtain ⟨-, hpk, -⟩ := h0
    exact hpk
  exact restWin_of_lvl (by linarith) (by linarith) (by linarith) hH CM winLvl (restWinNum_proved hS hpk CM hCM)
    (a_mem_win hS)

theorem theorem_A_closed_form_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound (restWinE_proved D)

end Formalism.MainNotions.G.GramWindowAlt

end
