module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelChordLawSumAndDifference
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicModel_chordLaw_sum_and_difference : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  first | exact @GlobalTheory.ThetaPar.Chord.model_chord | exact GlobalTheory.ThetaPar.Chord.model_chord | (intros; apply GlobalTheory.ThetaPar.Chord.model_chord <;> assumption)
