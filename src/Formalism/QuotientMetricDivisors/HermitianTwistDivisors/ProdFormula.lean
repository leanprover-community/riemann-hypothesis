module

public import Formalism.QuotientMetricDivisors.ProdFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem log_abs_norm_eq_two_sum (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (a : K) (ha : a ≠ 0) :
    Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ := by
  have h := NumberField.InfinitePlace.prod_eq_abs_norm a
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w))]
  have hpos : ∀ w : InfinitePlace K, w a ≠ 0 := fun w => by
    rw [← InfinitePlace.norm_embedding_eq]
    simpa using ha
  rw [← Rat.cast_abs, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (hpos w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hm, Real.log_pow, InfinitePlace.norm_embedding_eq]
  push_cast
  ring

theorem prod_formula' : ProdFormula := by
  intro K _ _ _ _ a ha
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have hvw : ∀ w : HeightOneSpectrum (𝓞 K), vw w a = FractionalIdeal.count K w I := fun w => rfl
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
    intro h0
    apply hw
    simp [hvw, h0]
  refine ⟨hfin.subset (by simpa using hsupp), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpos : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := fun w => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hN : (|Algebra.norm ℚ a| : ℚ) = ∏ w ∈ hfin.toFinset,
      ((Ideal.absNorm w.asIdeal : ℚ)) ^ FractionalIdeal.count K w I := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← hIdef]
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_, map_prod]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    · intro w hw
      simp only [Function.mem_mulSupport, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
      intro h0
      apply hw
      rw [h0, zpow_zero]
  have hlog : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ w ∈ hfin.toFinset,
      (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    have h1 : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w ∈ hfin.toFinset,
        ((Ideal.absNorm w.asIdeal : ℝ)) ^ FractionalIdeal.count K w I := by
      rw [← Rat.cast_abs, hN]
      push_cast
      rfl
    rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hpos w))]
    exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  have hB := log_abs_norm_eq_two_sum K a ha
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  calc (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖
      = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / finrank ℚ K := by
        rw [hB]
        field_simp
    _ = ∑ w ∈ hfin.toFinset, lw w * (vw w a : ℝ) := by
        rw [hlog, Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hvw, lw]
        ring

end Formalism.DivisionValues
