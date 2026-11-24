module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_mul_coeff_mem_S : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF τ i
  obtain ⟨w, hw, hF⟩ := hF
  have key : ∀ n, ‖coeff n ((i.factorial : K⟦X⟧) * coeff i (F τ))‖ * wS K e n =
      ‖algebraMap O K (emb t τ (w (i, n)))‖ := fun n => by
    rw [← hF τ i n, wS, ← norm_mul, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1; ring
  rw [mem_S]
  simp only [key]
  refine ⟨fun n => norm_algebraMap_le _, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt_one (K := K) l)
  have h : ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w (i, n) := by
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (f := fun n : ℕ => (i, n)) (fun _ _ _ _ h => by simpa using h)
  rw [Nat.cofinite_eq_atTop] at h
  filter_upwards [h] with n hn
  obtain ⟨c, hc⟩ := hn
  rw [Real.dist_eq, sub_zero, abs_norm, hc, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)) hr

end GlobalTheory.CrysPrism
