module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

namespace GlobalTheory.EigenvectorOfSum

theorem eigenvector_mem_of_sum_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ (g : I), ∀ y ∈ U, (T g : Y → Y) y ∈ U) (S : Finset α) (y : α → Y)
    (hy : ∀ a ∈ S, ∀ (g : I), (T g : Y → Y) (y a) = χ a g • y a)
    (hs : ∑ a ∈ S, y a ∈ U) : ∀ a ∈ S, y a ∈ U := by
  classical
  induction S using Finset.strongInduction generalizing y with
  | H S ih =>
  intro a ha
  by_cases hex : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, χ a g ≠ χ b g := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hba (hχ (funext hcon)).symm
    set y' : α → Y := fun c => (χ c g - χ b g) • y c with hyq
    have hy' : ∀ c ∈ S.erase b, ∀ g', (T g' : Y → Y) (y' c) = χ c g' • y' c := by
      intro c hc g'
      rw [hyq, map_smul, hy c (Finset.mem_of_mem_erase hc) g', smul_comm]
    have hs' : ∑ c ∈ S.erase b, y' c ∈ U := by
      have h1 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c ∈ U :=
        U.sub_mem (hU g _ hs) (U.smul_mem _ hs)
      have h2 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c = ∑ c ∈ S.erase b, y' c := by

        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hb]
        have hb0 : (T g : Y → Y) (y b) - χ b g • y b = 0 := by rw [hy b hb g, sub_self]
        rw [hb0, add_zero]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hyq]
        dsimp only
        rw [sub_smul, hy c (Finset.mem_of_mem_erase hc) g]
      rwa [h2] at h1
    have hmem := ih (S.erase b) (Finset.erase_ssubset hb) y' hy' hs' a
      (Finset.mem_erase.2 ⟨hba.symm, ha⟩)
    have hne : χ a g - χ b g ≠ 0 := sub_ne_zero.2 hg
    have h3 := U.smul_mem (χ a g - χ b g)⁻¹ hmem
    rwa [hyq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
  · simp only [ne_eq, not_exists, not_and, not_not] at hex
    have hS : S = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hex⟩
    subst hS
    simpa using hs

end GlobalTheory.EigenvectorOfSum
