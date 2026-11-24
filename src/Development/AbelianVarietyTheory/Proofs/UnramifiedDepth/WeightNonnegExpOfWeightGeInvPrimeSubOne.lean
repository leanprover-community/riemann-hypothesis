module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

@[expose] public section

open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)


variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ) in
theorem _root_.GlobalTheory.ExpWeight.weight_exp :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  intro C _ _ v l hl hvl σ _ _ ρ h h0 hh
  set c : ℝ := 1 / ((l : ℝ) - 1) with hc
  set w : (σ →₀ ℕ) → ℝ := fun α => α.sum (fun j e => ρ j * (e : ℝ)) with hw
  have hwadd : ∀ α β : σ →₀ ℕ, w (α + β) = w α + w β := fun α β => by
    simp only [hw]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  have hsumle : ∀ {ι : Type} (s : Finset ι) (f : ι → C) (r : ℝ),
      (∀ i ∈ s, ((r : ℝ) : WithTop ℝ) ≤ v (f i)) → ((r : ℝ) : WithTop ℝ) ≤ v (∑ i ∈ s, f i) := by
    intro ι s f r hf
    refine Finset.sum_induction f (fun x => ((r : ℝ) : WithTop ℝ) ≤ v x) (fun a b ha hb => ?_) ?_ hf
    · exact le_trans (le_min ha hb) (v.map_add a b)
    · simp
  have hpow : ∀ (d : ℕ) (α : σ →₀ ℕ), (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h ^ d)) := by
    intro d
    induction d with
    | zero =>
      intro α
      rw [pow_zero, MvPowerSeries.coeff_one]
      split_ifs with hα
      · subst hα
        simp [hw]
      · simp
    | succ d ih =>
      intro α
      rw [pow_succ, MvPowerSeries.coeff_mul]
      refine hsumle _ _ _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [v.map_mul]
      have e : ((((d + 1 : ℕ) : ℝ) * c - w α : ℝ) : WithTop ℝ) =
          (((d : ℝ) * c - w p.1 : ℝ) : WithTop ℝ) + ((1 / ((l : ℝ) - 1) - w p.2 : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← hp, hwadd, hc]
        congr 1
        push_cast
        ring
      rw [e]
      exact add_le_add (ih p.1) (hh p.2)
  intro α
  have hsub : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero h0
  rw [PowerSeries.coeff_subst hsub]
  refine finsum_induction (fun x => (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ v x) (by simp)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) fun d => ?_
  simp only [PowerSeries.coeff_exp, smul_eq_mul, v.map_mul]
  have hf : (d.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hinv : algebraMap ℚ C (1 / (d.factorial : ℚ)) = ((d.factorial : C))⁻¹ := by simp
  rw [hinv]
  obtain ⟨y, hy⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hf)
  have hfact := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hvl (Nat.factorial_ne_zero d)
  have hprod : v ((d.factorial : C))⁻¹ + v (d.factorial : C) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ hf, v.map_one]
  rw [hy, hfact, ← WithTop.coe_add, WithTop.coe_eq_zero] at hprod
  have hle := _root_.GlobalTheory.LegendreBounds.upper l hl d
  have hyr : y = -((d.factorial.factorization l : ℕ) : ℝ) := by linarith
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ hl] at hle
  have hdc : (d : ℝ) / ((l : ℝ) - 1) = d * c := by rw [hc]; ring
  rw [hy]
  calc (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ ((y + ((d : ℝ) * c - w α) : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr (by linarith)
    _ = ((y : ℝ) : WithTop ℝ) + (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) := WithTop.coe_add _ _
    _ ≤ _ := add_le_add le_rfl (hpow d α)

end GlobalTheory.ExpWeight
