module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.FnCrofton

theorem measurable_matrix_gaussian (m n : ℕ) :
    Measurable (matGauss : (Fin m → Fin n → ℂ) → ℝ≥0∞) := by
  unfold matGauss
  fun_prop

theorem measurable_cntOver_first {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S) :
    Measurable fun π : Fin (e + 1) → Fin n → ℂ => cntOver S π (firstCoordVec (e + 1)) := by
  have H := GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hS
  have H2 := H.comp (measurable_id.prodMk (measurable_const (a := firstCoordVec (e + 1))))
  exact H2

theorem encard_fibrePts_inter {n e : ℕ} (S A : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    (((fibrePts S π ∩ A).encard : ℕ∞) : ℝ≥0∞) = cntOver (S ∩ A) π (firstCoordVec (e + 1)) := by
  unfold cntOver
  congr 2
  ext y
  simp only [fibrePts, ptsOver, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

end ModelDimension.FnCrofton
