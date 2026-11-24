module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

section Tools

variable {R : Type u} [CommRing R]

theorem eq_substInv_of_right (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht0 : constantCoeff t = 0) (ht : s.subst t = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hT : HasSubst t := HasSubst.of_constantCoeff_zero' ht0
  have key := subst_comp_subst_apply hs hT (s.substInvOfIsUnit h1)
  rw [subst_substInvOfIsUnit_left s h0 h1, subst_X hT, ht, X_subst] at key
  exact key

theorem eq_substInv_of_left (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s))
    (t : R⟦X⟧) (ht : t.subst s = X) :
    t = s.substInvOfIsUnit h1 := by
  have hs : HasSubst s := HasSubst.of_constantCoeff_zero' h0
  have hq : HasSubst (s.substInvOfIsUnit h1) := HasSubst.substInvOfIsUnit s h1
  have key := subst_comp_subst_apply hs hq t
  rw [subst_substInvOfIsUnit_right s h0 h1, ht, subst_X hq, X_subst] at key
  exact key.symm

theorem compInv_eq_substInv (s : R⟦X⟧) (h0 : constantCoeff s = 0) (h1 : IsUnit (coeff 1 s)) :
    compInv s = s.substInvOfIsUnit h1 := by
  have hex : ∃ t : R⟦X⟧, constantCoeff t = 0 ∧ s.subst t = X :=
    ⟨s.substInvOfIsUnit h1, constantCoeff_substInvOfIsUnit s h1,
      subst_substInvOfIsUnit_right s h0 h1⟩
  unfold compInv
  rw [dite_eq_left hex]
  exact eq_substInv_of_right s h0 h1 _ hex.choose_spec.1 hex.choose_spec.2

end Tools

theorem composition_inverse_spec : CompInvSpec.{u} := by
  intro R _ s h0 h1
  rw [compInv_eq_substInv s h0 h1]
  refine ⟨constantCoeff_substInvOfIsUnit s h1, subst_substInvOfIsUnit_right s h0 h1,
    subst_substInvOfIsUnit_left s h0 h1, ?_, fun t ht0 ht => eq_substInv_of_right s h0 h1 t ht0 ht,
    fun t _ ht => eq_substInv_of_left s h0 h1 t ht⟩
  rw [coeff_one_substInvOfIsUnit]
  exact h1.val_inv_mul

theorem composition_inverse_map : CompInvMap.{u, v} := by
  intro R S _ _ φ s h0 h1
  have h0' : constantCoeff (PowerSeries.map φ s) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have h1' : IsUnit (coeff 1 (PowerSeries.map φ s)) := by
    rw [coeff_map]; exact h1.map φ
  rw [compInv_eq_substInv _ h0' h1', compInv_eq_substInv s h0 h1]
  apply eq_substInv_of_right _ h0' h1'
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_substInvOfIsUnit, map_zero]
  · have := PowerSeries.map_subst (HasSubst.substInvOfIsUnit s h1) (h := φ) s
    rw [subst_substInvOfIsUnit_right s h0 h1] at this
    rw [← PowerSeries.map_X φ]
    exact this.symm

theorem integration_spec : IntegSpec.{u} := by
  unfold IntegSpec
  intro K _ _ f
  have hc : ∀ n : ℕ, coeff (n + 1) (integ f) = coeff n f / ((n : K) + 1) := by
    intro n
    unfold integ
    simp
  have hd : PowerSeries.derivative (integ f) = f := by
    ext n
    rw [coeff_derivative, hc]
    have : ((n : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    field_simp
  refine ⟨?_, hd, ?_⟩
  · unfold integ
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  · intro g hg0 hg
    ext n
    cases n with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, hg0]
      unfold integ
      simp
    | succ k =>
      rw [hc]
      have h1 := congrArg (coeff k) hg
      rw [coeff_derivative] at h1
      have : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      rw [← h1]
      field_simp

end Formalism.L2.Th1.A
