module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
public import Formalism.PeriodIntegrals.FglGram
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubeRelationOfParallelogram
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GramUnit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.JetsPhW
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem ph0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.ph = 0 := by
  unfold G1.ph
  rw [map_neg, neg_eq_zero]
  show logMv _ 0 = 0
  unfold logMv
  simp

theorem fglData {p : ℕ} [Fact p.Prime] (g : G1 p) (h : g.Ok) : PI.FglGram.Data g.l g.ex g.ph :=
  ⟨h.2.2.1, h.2.2.2, ph0 g⟩

theorem cube_of_two_identities_holds : CubeOfTwoIdentities := by
  intro p _ g h
  exact cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)

theorem phGramG_holds : PhGramG := by
  first
  | exact phase_gram'
  | (intro p _ g; intros; apply phase_gram' <;> first | exact fglData g ‹_› | assumption)
  | (unfold PhGramG; done)

theorem gramUnitEq_holds : GramUnitEq := by
  first
  | exact gramExpansion_orthonormal
  | (intro p _ g; intros; apply gramExpansion_orthonormal <;> first | exact fglData g ‹_› | assumption)
  | (unfold GramUnitEq; done)

theorem jetsHigh_holds : JetsHigh :=
  fun p _ g hOk => jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsOne_holds : JetsOne :=
  fun p _ g hOk => jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsTwo_holds : JetsTwo :=
  fun p _ g a b hOk => jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1
    hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
