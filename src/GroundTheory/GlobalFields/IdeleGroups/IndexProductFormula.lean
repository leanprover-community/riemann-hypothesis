module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

theorem norm_natCast_adicCompletion_eq_one {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by
  have h := (FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v) (n : 𝓞 K)).2 hv
  rwa [map_natCast, map_natCast] at h

theorem finprod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := FinitePlace.prod_eq_inv_abs_norm hn'
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  have hpos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  push_cast
  rw [abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

theorem prod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) * (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset]
  · exact finprod_norm_natCast_adicCompletion_mul hn
  · intro v hv
    by_contra h
    exact hv (norm_natCast_adicCompletion_eq_one fun h' ↦ h (hS v h'))

theorem prod_norm_natCast_infinitePlaceCompletion_pow_mult (n : ℕ) :
    ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by
  have h := InfinitePlace.prod_eq_abs_norm (n : K)
  have hw : ∀ w : InfinitePlace K, ‖(n : w.Completion)‖ = w (n : K) := fun w ↦ by
    rw [← map_natCast (algebraMap K w.Completion) n, AbsoluteValue.Completion.algebraMap_def,
      AbsoluteValue.Completion.norm_coe, WithAbs.algebraMap_right_apply,
      WithAbs.ofAbs_toAbs, Algebra.algebraMap_self_apply, ← InfinitePlace.coe_apply]
  simp_rw [hw, h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  push_cast
  exact abs_of_nonneg (by positivity)

theorem prod_norm_natCast_mul_prod_infinitePlace {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by
  rw [prod_norm_natCast_infinitePlaceCompletion_pow_mult]
  exact prod_norm_natCast_adicCompletion_mul hn S hS

end GroundTheory.Global
