module

public import Formalism.LocalRingCardinality.DataTheta
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

@[expose] public section

namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by

        rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
