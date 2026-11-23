module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
