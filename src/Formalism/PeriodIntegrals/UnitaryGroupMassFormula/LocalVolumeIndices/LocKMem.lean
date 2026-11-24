module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocBEOfNatCast
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst)

theorem LocK_mem {ι : Type} (K2 : Set I.Gf) (hone : (1 : I.Gf) ∈ K2)
    (hmul : ∀ x ∈ K2, ∀ y ∈ K2, x * y ∈ K2) (g : ℕ) (hKg : ∀ x ∈ I.Kg g, x ∈ K2)
    (T : Finset ι) (χ : ι → Af I.F) (hid : ∀ p, χ p * χ p = χ p)
    (hort : ∀ p q, p ≠ q → χ p * χ q = 0) (c : Af I.F) (hc : c ∈ Formalism.UG.intAd I.F)
    (hgc : (g : Af I.F) * c = 1 - ∑ p ∈ T, χ p) (x : I.Gf) (hx : x ∈ I.Kset)
    (hloc : ∀ p ∈ T, locG I (χ p) x ∈ K2) : x ∈ K2 := by
  classical
  have key : ∀ S : Finset ι, S ⊆ T →
      (∑ p ∈ S, χ p) * (∑ p ∈ S, χ p) = ∑ p ∈ S, χ p ∧ locG I (∑ p ∈ S, χ p) x ∈ K2 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty, mul_zero, true_and]
      rw [LocB_locG_zero]; exact hone
    | insert q S hq ih =>
      intro hS
      obtain ⟨h1, h2⟩ := ih (fun p hp => hS (Finset.mem_insert_of_mem hp))
      have horth : χ q * ∑ p ∈ S, χ p = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun p hp => hort q p fun h => hq (h ▸ hp)
      rw [Finset.sum_insert hq]
      refine ⟨?_, ?_⟩
      · have e : (χ q + ∑ p ∈ S, χ p) * (χ q + ∑ p ∈ S, χ p) =
            χ q * χ q + χ q * (∑ p ∈ S, χ p) + χ q * (∑ p ∈ S, χ p) +
              (∑ p ∈ S, χ p) * (∑ p ∈ S, χ p) := by ring
        rw [e, hid, horth, h1]; ring
      · rw [← LocB_locG_add I _ _ (hid q) h1 horth]
        exact hmul _ (hloc q (hS (Finset.mem_insert_self q S))) _ h2
  obtain ⟨hT1, hT2⟩ := key T subset_rfl
  rw [← LocB_locG_split I _ hT1 x]
  exact hmul _ hT2 _ (hKg _ (LocB_Kg I g _ c hT1 hc hgc x hx))

end PI.MassDataKppVolLemmas
