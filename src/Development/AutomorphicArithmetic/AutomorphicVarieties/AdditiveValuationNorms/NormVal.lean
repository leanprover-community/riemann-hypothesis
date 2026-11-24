module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

private theorem dvd_of_norm_le' {l : ℕ} [Fact l.Prime] {d y : ℤ_[l]} (h : ‖y‖ ≤ ‖d‖) : d ∣ y := by
  by_cases hy : y = 0
  · subst hy
    exact dvd_zero d
  by_cases hd : d = 0
  · subst hd
    rw [norm_zero, norm_le_zero_iff] at h
    exact absurd h hy
  have hav : ∀ x : ℤ_[l], x ≠ 0 → IsDiscreteValuationRing.addVal ℤ_[l] x = x.valuation :=
    fun x hx => IsDiscreteValuationRing.addVal_def x (PadicInt.unitCoeff hx) PadicInt.irreducible_p _
      (PadicInt.unitCoeff_spec hx)
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hav d hd, hav y hy, Nat.cast_le]
  rw [PadicInt.norm_eq_zpow_neg_valuation hd, PadicInt.norm_le_pow_iff_le_valuation y hy] at h
  exact h

private theorem vl_prod {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) :
    vl l (∏ i ∈ s, f i) = ∑ i ∈ s, vl l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    exact IsDiscreteValuationRing.addVal_mul

theorem UpperTheory.V.PropA.normVal :
    ∀ (l : ℕ) [Fact l.Prime] (R c : ℕ) (d : ℤ_[l]) (x : Fin R → ℤ_[l]),
      ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) ≤ ‖d‖ → vl l d ≤ ∑ i, ((c : ℕ∞) + vl l (x i)) := by
  intro l _ R c d x h
  have h1 : ‖∏ i, ((l : ℤ_[l]) ^ c * x i)‖ = ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_mul, norm_pow, PadicInt.norm_p, inv_pow]
  have h2 : d ∣ ∏ i, ((l : ℤ_[l]) ^ c * x i) := dvd_of_norm_le' (h1 ▸ h)
  have h3 : vl l (∏ i, ((l : ℤ_[l]) ^ c * x i)) = ∑ i, ((c : ℕ∞) + vl l (x i)) := by
    rw [vl_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (PadicInt.irreducible_p (p := l)).addVal_pow c
    unfold vl
    rw [IsDiscreteValuationRing.addVal_mul, this]
  rw [← h3]
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h2
