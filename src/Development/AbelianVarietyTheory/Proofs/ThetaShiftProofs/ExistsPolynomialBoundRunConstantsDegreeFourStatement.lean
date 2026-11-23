module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFour
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ GlobalTheory.ArcCM.RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  first | exact @GlobalTheory.ArcCM.Room.room_four | exact GlobalTheory.ArcCM.Room.room_four | (intros; apply GlobalTheory.ArcCM.Room.room_four <;> assumption)
