module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] at h

theorem intIndex : GlobalTheory.SatakeWeyl.IntIndex := by
  intro L _ _ ϖ σ q hU
  obtain ⟨-, -, -, hϖ, -, -, hcard⟩ := hU
  set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv
  set A := v.valuationSubring
  set O := (intL L).toAddSubgroup
  let e : O →+ A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : O →+ A ⧸ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  have hϖ1 : v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change _ ↔ Ideal.Quotient.mk _ (e x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]
    change _ ↔ v x.1 < 1
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : v y ≤ 1 := hy
      rw [← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]
      calc WithZero.exp (-1 : ℤ) * v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact (lt_one_iff_le_exp_neg_one _).2 le_rfl
    · intro hx
      refine ⟨ϖ⁻¹ * x.1, ?_, ?_⟩
      · show v (ϖ⁻¹ * x.1) ≤ 1
        rw [map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]
        calc WithZero.exp (1 : ℤ) * v x.1 ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
              by gcongr; exact (lt_one_iff_le_exp_neg_one _).1 hx
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [AddMonoidHom.coe_mulLeft]
        show ϖ * (ϖ⁻¹ * x.1) = x.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact hcard

end GlobalTheory.SatakeWeyl
