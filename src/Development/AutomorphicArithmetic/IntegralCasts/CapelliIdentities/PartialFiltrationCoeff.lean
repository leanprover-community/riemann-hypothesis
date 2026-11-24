module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add (f := _)]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add (f := _)]
      exact Ideal.add_mem _ (hx n) (hy n)
