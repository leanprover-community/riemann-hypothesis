module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBounded
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.runScalars_ne_zero_and_log_bounded : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  first | exact @GlobalTheory.RunIn.scalOfP_size | exact GlobalTheory.RunIn.scalOfP_size | (intros; apply GlobalTheory.RunIn.scalOfP_size <;> assumption)
