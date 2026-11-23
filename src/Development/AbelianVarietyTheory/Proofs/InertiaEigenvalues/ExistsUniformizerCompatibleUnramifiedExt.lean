module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem exists_gen_of_valuation_eq (K : UQ) (x : K.E)
    (hx : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)) :
    ∃ a : K.O, algebraMap K.O K.E a = x ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {a} := by
  set v := IsDiscreteValuationRing.maximalIdeal K.O with hv
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := K.O) (K := K.E)
    (x := x) (by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  refine ⟨a, rfl, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hx
  have h1 : a ∈ v.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hx, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]; norm_num
  have h2 : a ∉ v.asIdeal ^ 2 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hx, WithZero.exp_le_exp]; norm_num
  change a ∈ IsLocalRing.maximalIdeal K.O at h1
  change a ∉ IsLocalRing.maximalIdeal K.O ^ 2 at h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hm := hϖ.maximalIdeal_eq
  rw [hm] at h1 h2 ⊢
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h1
  have hb : IsUnit b := by
    by_contra hb
    apply h2
    have : b ∈ IsLocalRing.maximalIdeal K.O := (IsLocalRing.mem_maximalIdeal b).2 hb
    rw [hm] at this
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    exact mul_dvd_mul (Ideal.mem_span_singleton.1 this) dvd_rfl
  rw [Ideal.span_singleton_mul_left_unit hb]

theorem exists_unif (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (h : IsUnrExt K K' d φ) :
    ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  obtain ⟨x, hx⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1) := hx
  obtain ⟨π, hπ, hm⟩ := exists_gen_of_valuation_eq K x hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact WithZero.exp_ne_zero hx'.symm
  have hv := h.2.2.1 x
  unfold val at hv
  rw [hx', WithZero.log_exp] at hv
  have hy0 : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by
    simpa using (map_ne_zero φ).2 hx0
  have hy : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) = WithZero.exp (-1) := by
    rw [← WithZero.exp_log hy0]; congr 1; omega
  obtain ⟨π', hπ', hm'⟩ := exists_gen_of_valuation_eq K' (φ x) hy
  exact ⟨π, π', by rw [hπ', hπ], hm, hm'⟩

end GlobalTheory.UnitLemma.Unr
