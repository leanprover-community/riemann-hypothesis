module

public import Formalism.IncomingBounds.StatementThmP
public import Mathlib.RingTheory.PowerSeries.Exp
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory

section

variable {C : Type} [Field C] [CharZero C] {σ : Type}

omit [CharZero C] in
theorem mvExp_coeff_apply (a : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := rfl

theorem mvExp_eq_subst_exp (a : MvPowerSeries σ C) (ha : MvPowerSeries.constantCoeff a = 0) :
    mvExp a = PowerSeries.subst a (PowerSeries.exp C) := by
  ext m
  rw [mvExp_coeff_apply, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    by_contra hk'
    apply hk
    have hlt : m.degree < k := by simpa using hk'
    have : MvPowerSeries.coeff m (a ^ k) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt)
        (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha))
    simp [this]

theorem mfact_mul_coeff_mvExp_linear [Fintype σ] (y : σ → C) (m : σ →₀ ℕ) :
    (mfact m : C) * MvPowerSeries.coeff m (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) =
      ∏ i ∈ m.support, y i ^ m i := by
  classical
  have hL : (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C)) =
      ((∑ s, y s • (MvPolynomial.X s : MvPolynomial σ C) : MvPolynomial σ C) : MvPowerSeries σ C) := by

    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.coe_mul,
      MvPolynomial.coe_C, MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdeg : (m.sum fun _ e => e) = m.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [mvExp_coeff_apply, hL, Finset.sum_eq_single m.degree]
  · rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : mfact m * m.multinomial = m.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : (mfact m : C) * (m.multinomial : C) = (m.degree.factorial : C) := by exact_mod_cast hs
    have h0 : (m.degree.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
    rfl
  · intro k _ hk
    rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

end

theorem mvExp_add_subst_linear : ∀ (C : Type) [Field C] [CharZero C] (σ : Type) [Fintype σ],
  (∀ a b : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 → mvExp (a + b) = mvExp a * mvExp b) ∧
  (∀ a : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → mvExp a = PowerSeries.subst a (PowerSeries.exp C)) ∧
  (∀ (τ : Type) [Fintype τ] (φ : σ → MvPowerSeries τ C) (a : MvPowerSeries σ C), (∀ s, MvPowerSeries.constantCoeff (φ s) = 0) → MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.subst φ (mvExp a) = mvExp (MvPowerSeries.subst φ a)) ∧
  (∀ (y : σ → C) (P : MvPolynomial σ C), jetAt0 P (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) = MvPolynomial.eval y P) := by
  intro C _ _ σ _
  refine ⟨fun a b ha hb => ?_, fun a ha => mvExp_eq_subst_exp a ha, fun τ _ φ a hφ ha => ?_, fun y P => ?_⟩
  · rw [mvExp_eq_subst_exp a ha, mvExp_eq_subst_exp b hb,
      mvExp_eq_subst_exp (a + b) (by rw [map_add (f := _), ha, hb, add_zero])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ha hb
  · have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
    rw [mvExp_eq_subst_exp a ha,
      mvExp_eq_subst_exp _ (MvPowerSeries.constantCoeff_subst_eq_zero hs hφ ha),
      PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const hs]
  · rw [MvPolynomial.eval_eq, jetAt0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc, mfact_mul_coeff_mvExp_linear]

end GlobalTheory
