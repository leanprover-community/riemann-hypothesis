module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoLowsDistanceBounds
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_lows_distance_bounds : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  first | exact @GlobalTheory.ExpTie.Lift.low_dist | exact GlobalTheory.ExpTie.Lift.low_dist | (intros; apply GlobalTheory.ExpTie.Lift.low_dist <;> assumption)
