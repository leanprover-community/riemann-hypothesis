module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
