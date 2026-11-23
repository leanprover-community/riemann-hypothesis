module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseIntegral
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseLift
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
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem denseBoundedHeight : DenseBoundedHeight.Statement := by
  intro ι _ _ n P
  obtain ⟨c, hc⟩ := P.exists_chart
  obtain ⟨s, g0, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (P.ChartAlg c)
  let b : Coord n → P.ChartAlg c := fun v ↦ (P.chartMap c).rangeRestrict (X v)
  choose δ R hδ hR hbd using fun v ↦ exists_integral_bound g0 hint (b v)
  set Δ : ℕ := ∏ v, δ v with hΔ
  set R0 : ℝ := 1 + ∑ v, R v with hR0
  have hΔpos : 0 < Δ := Finset.prod_pos fun v _ ↦ hδ v
  have hRnn : ∀ v, 0 ≤ R v := fun v ↦ zero_le_one.trans (hR v)
  have hR0pos : 0 < R0 := by
    have := Finset.sum_nonneg fun v (_ : v ∈ Finset.univ) ↦ hRnn v
    linarith
  refine ⟨{z | ∃ ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (X j)) ^ N = 1) ∧ z = P.chartPoint c ψ},
    ∑ k, (Real.log Δ + Real.log (Real.sqrt (n k + 1) * R0)), ?_, ?_, ?_⟩
  · rintro z ⟨ψ, -, rfl⟩
    exact P.chartPoint_mem c hc ψ
  · intro m f hf hvan
    by_contra hfP
    have hg := P.chartMap_ne_zero c hc hf hfP
    obtain ⟨ψ, hψ, hroots⟩ := exists_algHom_rootsOfUnity_ne_zero g0 hinj hint hg
    apply hψ
    rw [← P.evalCone_chartPoint c ψ f]
    exact hvan _ ⟨ψ, hroots, rfl⟩
  · rintro z ⟨ψ, hroots, rfl⟩
    refine height_standard_le (P.chartPoint c ψ) (P.chartPoint_mem c hc ψ).1 hΔpos hR0pos ?_ ?_
    · intro k i
      have h1 := (hbd ⟨k, i⟩ ψ hroots).1
      have h2 : (Δ : AlgebraicClosure ℚ) * P.chartPoint c ψ k i =
          ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ) *
            ((δ ⟨k, i⟩ : AlgebraicClosure ℚ) * ψ (b ⟨k, i⟩)) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
        rfl
      rw [h2]
      have h3 : IsIntegral ℤ (((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ)) := by
        have := isIntegral_algebraMap (R := ℤ) (A := AlgebraicClosure ℚ)
          (x := ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : ℤ))
        simpa using this
      exact h3.mul h1
    · intro σ k i
      calc ‖σ (P.chartPoint c ψ k i)‖ ≤ R ⟨k, i⟩ := (hbd ⟨k, i⟩ ψ hroots).2 σ
        _ ≤ ∑ v, R v := Finset.single_le_sum (fun v _ ↦ hRnn v) (Finset.mem_univ _)
        _ ≤ R0 := by linarith

end

end GroundTheory.Heights₂.Heights
