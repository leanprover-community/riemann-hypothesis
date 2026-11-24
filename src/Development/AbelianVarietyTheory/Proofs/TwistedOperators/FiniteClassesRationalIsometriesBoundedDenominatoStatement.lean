module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominato
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧ ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  first | exact @GlobalTheory.HeckeEx.QFin.finite_reps | exact GlobalTheory.HeckeEx.QFin.finite_reps | (intros; apply GlobalTheory.HeckeEx.QFin.finite_reps <;> assumption)
