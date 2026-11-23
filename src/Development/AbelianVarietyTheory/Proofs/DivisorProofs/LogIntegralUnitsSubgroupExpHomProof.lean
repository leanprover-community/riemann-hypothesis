module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh

section Unit

variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem expU_add (s t : MvPowerSeries σ C) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    PowerSeries.subst (s + t) (PowerSeries.exp C) =
      PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])
  have comp : ∀ p : MvPowerSeries (Fin 2) C, constantCoeff p = 0 →
      MvPowerSeries.subst ![s, t] (PowerSeries.subst p (PowerSeries.exp C)) =
        PowerSeries.subst (MvPowerSeries.subst ![s, t] p) (PowerSeries.exp C) := by
    intro p hp
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hst]
  have H := congrArg (MvPowerSeries.subst ![s, t]) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [MvPowerSeries.subst_mul hst, comp _ (by simp), comp _ (by simp), comp _ (by simp),
    MvPowerSeries.subst_add hst, MvPowerSeries.subst_X hst, MvPowerSeries.subst_X hst] at H
  simpa using H

theorem cc_expU (s : MvPowerSeries σ C) (hs : constantCoeff s = 0) :
    constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [map_pow, hs, zero_pow he]

theorem expU_zero : PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  have h := expU_add (0 : MvPowerSeries σ C) 0 (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_expU _ (by simp)]
    exact isUnit_one
  exact hu.mul_left_cancel (by rw [mul_one]; exact h.symm)

omit [CharZero C] in
theorem inv_int (v : AddValuation C (WithTop ℝ)) (U : MvPowerSeries σ C) (hU : MvIsInt v U)
    (h1 : constantCoeff U = 1) : ∃ U', MvIsInt v U' ∧ U * U' = 1 := by
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let U' : MvPowerSeries σ S := fun α => ⟨coeff α U, hU α⟩
  have hU' : map S.subtype U' = U := by ext α; rfl
  have hc : constantCoeff U' = ((1 : Sˣ) : S) := by
    apply Subtype.ext
    change coeff 0 U = 1
    rw [coeff_zero_eq_constantCoeff_apply, h1]
  refine ⟨map S.subtype (invOfUnit U' 1), fun α => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff α (invOfUnit U' 1)).2
  · rw [← hU', ← map_mul, mul_invOfUnit U' 1 hc, map_one]

theorem unitSt : UnitSt := by
  intro C _ _ v σ _
  have hexp0 := expU_zero (C := C) (σ := σ)
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, fun s t hs ht => expU_add s t hs ht, fun s hs => cc_expU s hs,
    fun U hU h1 => inv_int v U hU h1⟩
  · rw [hexp0]; exact Subring.one_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ)
  · rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], ?_⟩
    rw [expU_add s t hs0 ht0]
    exact Subring.mul_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ) hs ht
  · rintro s ⟨hs0, hs⟩
    have hn0 : constantCoeff (-s) = 0 := by simp [hs0]
    refine ⟨hn0, ?_⟩
    obtain ⟨U', hU', hm⟩ := inv_int v _ hs (cc_expU s hs0)
    have e : PowerSeries.subst (-s) (PowerSeries.exp C) * PowerSeries.subst s (PowerSeries.exp C) = 1 := by
      rw [← expU_add _ _ hn0 hs0, neg_add_cancel, hexp0]
    have : PowerSeries.subst (-s) (PowerSeries.exp C) = U' := by
      calc PowerSeries.subst (-s) (PowerSeries.exp C)
          = PowerSeries.subst (-s) (PowerSeries.exp C) * (PowerSeries.subst s (PowerSeries.exp C) * U') := by
            rw [hm, mul_one]
        _ = U' := by rw [← mul_assoc, e, one_mul]
    rw [this]; exact hU'

end Unit

end GlobalTheory.IsoTriv
