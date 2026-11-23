module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

set_option backward.proofsInPublic true in
theorem jumpSum_support_subset {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (hR : Antitone R)
    (m : ℕ) (hm : R m = ⊥) :
    Function.support (fun t : ℕ => by classical exact if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)) ⊆
      ↑(Finset.range m) := by
  classical
  intro t ht
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push_neg at h
  apply ht
  have h1 : R t = ⊥ := le_bot_iff.mp (hm ▸ hR h)
  simp [h1]

theorem jumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R →
    (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBA
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hC]
  · by_cases hB : A ⊓ R t ≤ B
    · have heq : B ⊓ R t = A ⊓ R t :=
        le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)
      have hC' : ¬ B ⊓ R t ≤ C := by rw [heq]; exact hC
      simp [hC, hC', heq]
    · simp [hC, hB]

end GlobalTheory.PMon.Ram
