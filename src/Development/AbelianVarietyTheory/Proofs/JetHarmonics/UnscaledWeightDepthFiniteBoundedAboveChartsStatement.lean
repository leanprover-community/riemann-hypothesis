module

public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveCharts
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthBd.nuWt_bounds | exact GlobalTheory.DepthBd.nuWt_bounds | (intros; apply GlobalTheory.DepthBd.nuWt_bounds <;> assumption)
