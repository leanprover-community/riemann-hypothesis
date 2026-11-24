module

public import Formalism.ThetaLiftIndependence.Statement
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

open scoped BigOperators

namespace Formalism.ThetaLiftIndependence

namespace GaussOperatorLemmas

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

theorem sum_units_eq_sub {M : Type*} [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)

theorem sum_units_char (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])

theorem core (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp

end GaussOperatorLemmas

open GaussOperatorLemmas in
theorem gaussOp_eq : GaussOp := by
  intro 𝔽 V _ _ _ _ _ ψ ρ hψ v hv
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) •
        ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) *
        ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv

end Formalism.ThetaLiftIndependence
