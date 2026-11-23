module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFin
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField

theorem resFin_holds : ResFin := by
  intro E _ _ V _ _ _ _ Λ hΛ c hc
  have hZ : (Λ.restrictScalars ℤ).FG := by
    first
      | exact Submodule.FG.restrictScalars hΛ
      | (obtain ⟨t, ht⟩ := hΛ
         obtain ⟨s0, hs0⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
         rw [← ht, ← Submodule.span_smul_of_span_eq_top hs0]
         exact Submodule.fg_def.2 ⟨_, s0.finite_toSet.smul t.finite_toSet, rfl⟩)
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hmem : ∀ x ∈ Λ, ∃ a : Fin n → ℤ, ∑ i, a i • g i = x := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx'
    exact hx'
  haveI : NeZero c := ⟨by omega⟩
  refine ⟨Fin n → ZMod c, inferInstance,
    fun x => if hx : x ∈ Λ then fun i => (((hmem x hx).choose i : ℤ) : ZMod c) else 0, ?_⟩
  intro x hx y hy hxy
  beta_reduce at hxy
  rw [dite_eq_left hx, dite_eq_left hy] at hxy
  have hax := (hmem x hx).choose_spec
  have hby := (hmem y hy).choose_spec
  have hdiv : ∀ i, (c : ℤ) ∣ (hmem y hy).choose i - (hmem x hx).choose i := fun i => by
    have hi := congrFun hxy i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    exact hi
  choose k hk using hdiv
  refine ⟨∑ i, k i • g i, ?_, ?_⟩
  · have hs : ∑ i, k i • g i ∈ Submodule.span ℤ (Set.range g) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [hg] at hs
    exact hs
  · rw [← hax, ← hby, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, hk i, mul_smul, Nat.cast_smul_eq_nsmul E, natCast_zsmul]

end PI.TermsAtPtFiniteW
