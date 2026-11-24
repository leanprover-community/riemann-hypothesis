module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.ValRing

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isPrime_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (mCoordIdeal z).IsPrime :=
  RingHom.ker_isPrime _

theorem eval_ne_zero_of_notMem {z : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) :
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  intro h0
  refine hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using h0

theorem aeval_ne_zero_of_notMem {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) : aeval x h ≠ 0 := fun h0 =>
  eval_ne_zero_of_notMem hh hn
    (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))

theorem exists_isValueAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    ∃ v, IsValueAt x s z v := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  exact ⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq,
    eval_ne_zero_of_notMem hh hn, rfl⟩

theorem isValueAt_add {x : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt x s z v) (hw : IsValueAt x t z w) : IsValueAt x (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']
    exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_add (f := _), map_mul, heq, heq']; ring
  · simp only [map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem regAt_mul {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  rw [map_mul, map_mul, heq, heq']; ring

theorem regAt_add {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s + t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  · rw [add_comm d d']
    exact isMultiHomog_mul hg' hh
  · simp only [map_add (f := _), map_mul, heq, heq']; ring

theorem one_notMem_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (1 : MRing ι) ∉ mCoordIdeal z :=
  (Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top

theorem regAt_zero (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 0 :=
  ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem regAt_one (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 1 :=
  ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem isValueAt_zero_self (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt x 0 z 0 :=
  ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end

theorem regAt_valAt_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → RegAt x (mCoordIdeal z) 0 ∧ RegAt x (mCoordIdeal z) 1 ∧ valAt x 0 z = 0 ∧ valAt x 1 z = 1 ∧ ∀ s t : Ω, RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) t → RegAt x (mCoordIdeal z) (s * t) ∧ RegAt x (mCoordIdeal z) (s + t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z ∧ valAt x (s + t) z = valAt x s z + valAt x t z := by
  intro K _ ι _ Ω _ x z hz
  refine ⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z),
    valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]

end GlobalTheory.CompanionTheory.Ar.PB.ValRing
