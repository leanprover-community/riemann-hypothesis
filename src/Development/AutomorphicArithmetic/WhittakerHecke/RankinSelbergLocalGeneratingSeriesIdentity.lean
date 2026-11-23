module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private def UpperTheory.powerSeriesFirstDifferenceSeq (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => f 0
  | k + 1 => f (k + 1) - a * f k

private theorem UpperTheory.power_series_mul_linear (a : ℂ) (f : ℕ → ℂ) :
    PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk (UpperTheory.powerSeriesFirstDifferenceSeq a f) := by
  have h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X) := by ring
  rw [h]
  ext k
  cases k with
  | zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]
  | succ k =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [UpperTheory.powerSeriesFirstDifferenceSeq]

private theorem UpperTheory.geometric_sum_recurrence (x y : ℂ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), x ^ i * y ^ (k + 1 - i)) =
      x ^ (k + 1) + y * ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.succ_sub hi', pow_succ]
  ring

private theorem UpperTheory.product_four_geometric_series (x y x' y' c : ℂ) (S T : ℕ → ℂ)
    (hS0 : S 0 = 1) (hT0 : T 0 = 1)
    (hS : ∀ k, S (k + 1) = x ^ (k + 1) + y * S k)
    (hT : ∀ k, T (k + 1) = x' ^ (k + 1) + y' * T k) :
    (PowerSeries.mk fun k : ℕ => c ^ k * S k * T k) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear,
    UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]
  have hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k := fun k => by
    rw [hS (k + 1), hS k]; ring
  have hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k := fun k => by
    rw [hT (k + 1), hT k]; ring
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]
    ring

theorem UpperTheory.rankinSelberg_local_generating_series_identity :
    ∀ x y x' y' c : ℂ, (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)) * (∑ i ∈ Finset.range (k + 1), (x') ^ i * (y') ^ (k - i))) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  intro x y x' y' c
  exact UpperTheory.product_four_geometric_series x y x' y' c
    (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i))
    (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i))
    (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y')
