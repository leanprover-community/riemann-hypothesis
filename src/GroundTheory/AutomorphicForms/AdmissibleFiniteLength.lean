module

public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.AutomorphicForms.CuspidalAdmissible
public import GroundTheory.AutomorphicForms.IwahoriFactorization
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem fixedVectors_jacquetRep_congruenceSubgroup (m : ℕ) :
    fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) =
      fixedVectors (jacquetAction F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  ext x
  simp only [mem_fixedVectors]
  refine forall₂_congr fun y hy => ?_
  rw [jacquetRep, twist_apply, MonoidHom.comp_apply,
    invSqrtModular_leviIncl_of_mem y (congruenceSubgroup_le F n m (Subgroup.mem_subgroupOf.1 hy)),
    one_smul]

theorem isAdmissible_jacquetRep (hπ : IsAdmissible π) : IsAdmissible (jacquetRep F n β π) := by
  refine ⟨isSmooth_jacquetRep π hπ.1, fun L hLc hLo => ?_⟩
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hLo.mem_nhds L.one_mem)
  set m := max m₁ 1
  have hle : (congruenceSubgroup F n m).subgroupOf (levi F n β) ≤ L := fun x hx =>
    hm₁ (Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (le_max_left _ _)
      (Subgroup.mem_subgroupOf.1 hx)))
  have : FiniteDimensional ℂ (fixedVectors π (congruenceSubgroup F n m)) :=
    hπ.2 _ (isCompact_congruenceSubgroup F n m) (isOpen_congruenceSubgroup F n m)
  have hfin : FiniteDimensional ℂ
      (fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β))) := by
    rw [fixedVectors_jacquetRep_congruenceSubgroup]
    exact Module.Finite.of_surjective _
      (jacquetFixedMap_surjective_congruenceSubgroup β hπ (le_max_right m₁ 1))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)

end Parabolic

end GroundTheory.Automorphic
