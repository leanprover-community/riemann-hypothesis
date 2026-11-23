module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_int_of_degree_lt :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ V d I J _ _ G S t ht N e he μ hμ c
  have hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b) := fun b j =>
    S.co_int (fun n => by
      cases n with
      | inl x => exact he j x
      | inr κ => exact VF.Ge.zero 0) b
  obtain ⟨h0, h1, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e
    (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b)
    (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b)
    (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).symm)
    (fun c b => by simp)
    (fun c k x hk => by
      have hk' : k ≠ 0 := by omega
      simp only [if_neg hk', Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  have h2 := h1 c μ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h2
  · simp only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ] at h2

    rw [h2, map_sum]
    refine VF.Ge.sum fun j _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine (hz c j).mul_int ?_
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · intro s _
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPowerSeries.coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) _
    exact_mod_cast lt_of_lt_of_le hμ this

end GlobalTheory.MainTerm
