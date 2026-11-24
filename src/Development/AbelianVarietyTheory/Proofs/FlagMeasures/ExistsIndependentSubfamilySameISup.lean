module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem indep_subfamily_of_disjoint_or_le : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  intro ι M _ _ N h F
  classical
  refine Finset.induction_on F ?_ ?_
  · exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  · intro i F hi ih
    obtain ⟨J, hJF, hJsup, huniq⟩ := ih
    have hiJ : i ∉ J := fun hh => hi (hJF hh)
    rcases h i J with hd | hle
    · refine ⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩
      · rw [Finset.iSup_insert, Finset.iSup_insert, hJsup]
      · intro f f' hf hf' hsum
        rw [Finset.sum_insert hiJ, Finset.sum_insert hiJ] at hsum
        have hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j := by
          rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
        have hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j := by
          refine ⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _))
            (hf' i (Finset.mem_insert_self _ _)), ?_⟩
          rw [hdiff]
          exact Submodule.sub_mem _
            (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj))
            (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))
        rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
        rw [hmem] at hsum
        have hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j := add_left_cancel hsum
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hmem
        · exact huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk))
            (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj
    · refine ⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩
      rw [Finset.iSup_insert, ← hJsup]
      exact (sup_eq_right.mpr hle).symm

end GlobalTheory
