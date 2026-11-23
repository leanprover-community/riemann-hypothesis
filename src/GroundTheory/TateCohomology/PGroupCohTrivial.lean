module

public import GroundTheory.TateCohomology.CohTrivialBasic
public import GroundTheory.TateCohomology.DimensionShift
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep
open scoped MonoidAlgebra

universe u

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_cohTrivial_of_isZero_of_shift (P : Rep.{u} k G → Prop)
    (hcoind : ∀ M, P M → P (coindShift M)) (hind : ∀ M, P M → P (indShift M))
    (hbase : ∀ M, P M → IsZero (tateCohomology M (-2)) → TateAcyclic M ∧ CohTrivial M)
    (q : ℤ) (M : Rep.{u} k G) (hM : P M) (hq : IsZero (tateCohomology M q)) :
    TateAcyclic M ∧ CohTrivial M := by
  refine Int.inductionOn' (motive := fun q => ∀ M : Rep.{u} k G, P M →
    IsZero (tateCohomology M q) → TateAcyclic M ∧ CohTrivial M) q (-2) hbase ?_ ?_ M hM hq
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (coindShift M) n) := hq.of_iso (coindShiftIso M n)
    obtain ⟨t, c⟩ := ih (coindShift M) (hcoind M hM) h1
    have hS := coindSES_shortExact M
    have t2 : TateAcyclic (coindSES.obj M).X₂ := tateAcyclic_coindSES_X₂ M
    have c2 : CohTrivial (coindSES.obj M).X₂ := by
      rw [coindSES_obj_X₂]; exact cohTrivial_coind_bot _
    have t1 := TateAcyclic.of_shortExact_X₃ hS t2 t
    have c1 := CohTrivial.of_shortExact_X₃ hS c2 c
    rw [coindSES_obj_X₁] at t1 c1
    exact ⟨t1, c1⟩
  · intro n _ ih M hM hq
    have h1 : IsZero (tateCohomology (indShift M) n) := by
      have h := hq.of_iso (indShiftIso M (n - 1)).symm
      rwa [sub_add_cancel] at h
    obtain ⟨t, c⟩ := ih (indShift M) (hind M hM) h1
    have hS := indSES_shortExact M
    have t2 : TateAcyclic (indSES.obj M).X₂ := tateAcyclic_indSES_X₂ M
    have c2 : CohTrivial (indSES.obj M).X₂ := by
      rw [indSES_obj_X₂]; exact cohTrivial_ind_bot _
    have t3 := TateAcyclic.of_shortExact_X₁ hS t2 t
    have c3 := CohTrivial.of_shortExact_X₁ hS c2 c
    rw [indSES_obj_X₃] at t3 c3
    exact ⟨t3, c3⟩

end Shift

section Field

variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

end Field

end GroundTheory.GroupCoh
