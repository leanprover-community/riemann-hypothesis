module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSlopeSqLocalMatricesEqDeterminants
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ), IsAdelic A → (∀ σ, (Y σ).det ≠ 0) → (∀ σ, ‖(Y ((starRingEnd ℂ).comp σ)).det‖ = ‖(Y σ).det‖) → slope_sq (matNorm Y) (locLat A) = 2 * detDeg A Y / (Fintype.card ι : ℝ) := by
  first | exact @GlobalTheory.LocMatSlope.slope_sq_locLat | exact GlobalTheory.LocMatSlope.slope_sq_locLat | (intros; apply GlobalTheory.LocMatSlope.slope_sq_locLat <;> assumption)
