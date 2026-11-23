module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamily
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

theorem _root_.GlobalTheory.T.shareSize_bounds_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) := by
  first | exact @GlobalTheory.ShareNumbers.numbers_along_family | exact GlobalTheory.ShareNumbers.numbers_along_family | (intros; apply GlobalTheory.ShareNumbers.numbers_along_family <;> assumption)
