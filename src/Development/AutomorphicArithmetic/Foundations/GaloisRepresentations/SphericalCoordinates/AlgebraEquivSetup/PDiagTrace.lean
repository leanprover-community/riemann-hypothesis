module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
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
public import Mathlib.RingTheory.Complex
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]

  rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
