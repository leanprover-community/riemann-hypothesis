module

public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_kill_high_order :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∃ N : ℕ, ∀ f : MvPowerSeries σ k,
          (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → φ f = 0 := by
  intro k _ σ _ A _ _ φ hφ
  classical
  haveI := Fintype.ofFinite σ
  choose m hm using hφ
  set M := Finset.univ.sup m with hMdef
  have hM : ∀ i, φ (X i) ^ M = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hm i)
  refine ⟨Fintype.card σ * M + 1, fun f hf => ?_⟩

  let fi : σ → MvPowerSeries σ k := fun i α =>
    if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0
  have hcoeff : ∀ i α, coeff α (fi i) =
      if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0 :=
    fun i α => rfl
  have hsum : f = ∑ i, fi i := by
    ext α

    rw [map_sum]
    simp only [hcoeff]
    by_cases h : ∃ j, M ≤ α j
    · simp only [dif_pos h]
      rw [Finset.sum_ite_eq]
      simp
    · simp only [dif_neg h, Finset.sum_const_zero]
      apply hf
      push_neg at h
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, α i ≤ ∑ _i : σ, M := Finset.sum_le_sum fun i _ => (h i).le
        _ = Fintype.card σ * M := by simp
        _ < Fintype.card σ * M + 1 := Nat.lt_succ_self _
  have hdvd : ∀ i, (X i : MvPowerSeries σ k) ^ M ∣ fi i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro α hα
    rw [hcoeff]
    split_ifs with h h'
    · exact absurd (h'.symm ▸ h.choose_spec) (not_le.mpr hα)
    · rfl
    · rfl

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨g, hg⟩ := hdvd i
  rw [hg, map_mul, map_pow, hM i, zero_mul]

end GlobalTheory
