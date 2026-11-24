module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ) (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) := by
  first | exact @GlobalTheory.CM.LieMetricConj.form_conj | exact GlobalTheory.CM.LieMetricConj.form_conj | (intros; apply GlobalTheory.CM.LieMetricConj.form_conj <;> assumption)
