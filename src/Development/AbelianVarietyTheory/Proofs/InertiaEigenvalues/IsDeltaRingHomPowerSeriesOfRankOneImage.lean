module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemDeltaCommuteLocusSubringOfIsHausdorffStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TruncationDivisibility

theorem deltaS_X (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] : (deltaS l a).δ (X : (Wq l a)⟦X⟧) = 0 := by
  have h := (deltaS l a).φ_eq X
  have h2 : (deltaS l a).φ X = X ^ l := by
    change (Delta.ofLift l (frobS l a) _ _).φ X = _
    rw [Delta.ofLift_φ, frobS_X]
  rw [h2] at h
  have h3 : (l : (Wq l a)⟦X⟧) * (deltaS l a).δ X = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l a)

theorem X_pow_dvd_sub_trunc' {R : Type} [CommRing R] (x : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ x - (trunc n x : R⟦X⟧) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]

end GlobalTheory.TruncationDivisibility

open GlobalTheory.TruncationDivisibility in
theorem GlobalTheory.sdelta_of_rank_one : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hH σ e he hX
  set S := δLocus (deltaS l a) DC σ with hS
  have hXS : (X : (Wq l a)⟦X⟧) ∈ S := by
    rw [mem_δLocus, deltaS_X, map_zero, hX]
  have hCS : ∀ w : Wq l a, PowerSeries.C w ∈ S := GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff l a C DC J hl hH σ
  have hpoly : ∀ p : Polynomial (Wq l a), ((p : (Wq l a)⟦X⟧)) ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C w => rw [Polynomial.coe_C]; exact hCS w
    | add p q hp hq => rw [Polynomial.coe_add]; exact S.add_mem hp hq
    | monomial n w _ =>
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact S.mul_mem (hCS w) (S.pow_mem hXS _)
  refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l ((Wq l a)⟦X⟧) C (deltaS l a) DC (J.comap σ) J σ ?_ Ideal.map_comap_le hH ?_
  · rw [Ideal.mem_comap, map_natCast]; exact hl
  · intro x n
    refine ⟨_, hpoly (trunc (e * n) x), ?_⟩
    obtain ⟨c, hc⟩ := X_pow_dvd_sub_trunc' x (e * n)
    rw [hc, pow_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ n)
    rw [Ideal.mem_comap, map_pow]; exact he
