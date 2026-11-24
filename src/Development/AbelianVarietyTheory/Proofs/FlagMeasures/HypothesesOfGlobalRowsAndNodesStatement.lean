module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodes
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.hypotheses_of_global_rows_and_nodes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Glob0 D x eps CD Cg → Nodes D x eps → (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) → StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  first | exact @GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | exact GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | (intros; apply GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds <;> assumption)
