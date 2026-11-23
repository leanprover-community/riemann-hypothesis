module

public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

attribute [local instance] locRel

theorem norm_le_one_of_monic_root (P : Polynomial (PadicAlgCl p)) (hP : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1)
    {x : PadicAlgCl p} (hx : P.eval x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have key : ∀ m, ‖∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i‖ ≤ ‖x‖ ^ m := by
    intro m
    induction m with
    | zero => simpa using hc 0
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine (norm_add_le_max_padic _ _).trans (max_le ?_ ?_)
      · exact ih.trans (pow_le_pow_right₀ hlt.le (Nat.le_succ m))
      · rw [norm_mul, norm_pow]
        calc ‖P.coeff (m + 1)‖ * ‖x‖ ^ (m + 1) ≤ 1 * ‖x‖ ^ (m + 1) := by gcongr; exact hc _
          _ = ‖x‖ ^ (m + 1) := one_mul _
  have he := P.eval_eq_sum_range (x := x)
  rw [hx] at he
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · rw [h0] at he
    simp [hP.coeff_natDegree ▸ (show P.coeff 0 = P.coeff P.natDegree by rw [h0])] at he
  · obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
    rw [hm, Finset.sum_range_succ, ← hm, hP.coeff_natDegree, one_mul, hm] at he
    have e2 : x ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), P.coeff i * x ^ i := by
      linear_combination -he
    have := key m
    rw [← norm_neg, ← e2, norm_pow] at this
    have h3 : ‖x‖ ^ m < ‖x‖ ^ (m + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self m)
    linarith

end ReciprocityTheory.Neutral.Cmp
