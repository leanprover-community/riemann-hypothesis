module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe

private theorem mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type} [Field F]
    (w : (Σ k, ι k) → F) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap w h = MvPolynomial.C (MvPolynomial.aeval w h) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
  have key : ∀ m ∈ h.support, (∏ p : (Σ k, ι k), (MvPolynomial.C (w p) * MvPolynomial.X p.1 : MvPolynomial K F) ^ m p)
      = MvPolynomial.C (∏ p, w p ^ m p) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
    intro m hm
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    · rw [map_prod]
      simp only [map_pow]
    · rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hh m hm k]
  simp only [mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']

  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [key m hm, map_mul, ← mul_assoc]
  congr 2

private theorem aeval_eq_eval_map_intCast {K : Type} {ι : K → Type} (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem exists_isValueAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {t : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    (ht : RegAt x (mCoordIdeal z) t) : ∃ v, IsValueAt x t z v := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := ht
  have hz0 : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hQ
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog z hh, aeval_eq_eval_map_intCast, h0, map_zero, zero_mul]
  have hx0 : MvPolynomial.aeval x h ≠ 0 := by
    intro h0
    apply hz0
    exact hz.2 h (by rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog x hh, h0, map_zero, zero_mul])
  refine ⟨MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) /
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h), ?_⟩
  unfold IsValueAt
  exact ⟨d, g, h, hg, hh, hx0, he, hz0, rfl⟩

theorem valAt_ne_zero_of_regAt_inv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → s ≠ 0 →
    RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) s⁻¹ → valAt x s z ≠ 0 := by
  intro K _ ι _ Ω _ x s z hz hs h1 h2
  obtain ⟨v, hv⟩ := exists_isValueAt_of_regAt hz h1
  obtain ⟨w, hw⟩ := exists_isValueAt_of_regAt hz h2
  have hvw := isValueAt_mul hv hw
  rw [mul_inv_cancel₀ hs] at hvw
  have hone : IsValueAt x 1 z 1 := by
    unfold IsValueAt
    exact ⟨0, MvPolynomial.C 1, MvPolynomial.C 1, isMultiHomog_C_zero 1, isMultiHomog_C_zero 1,
      by simp, by simp, by simp, by simp⟩
  have h11 := isValueAt_unique hz hvw hone
  rw [valAt_eq hz hv]
  intro hv0
  rw [hv0, zero_mul] at h11
  exact zero_ne_one h11

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe
