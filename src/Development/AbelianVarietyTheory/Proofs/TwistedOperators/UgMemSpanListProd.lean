module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_mem_span_listProd (p q : ℕ) (u : Ug p q) :
    u ∈ Submodule.span ℂ {u : Ug p q | ∃ l : List (Mat p q), u = (l.map (ugι p q)).prod} := by
  have htop : Algebra.adjoin ℂ (Set.range (ugι p q)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Mat p q)) :=
      RingCon.mkₐ_surjective _
    obtain ⟨t, rfl⟩ := hs x
    induction t using TensorAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | ι y => exact Algebra.subset_adjoin ⟨y, rfl⟩
    | mul a b ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
    | add a b ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
  have hu : u ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (ugι p q))) := by
    rw [Subalgebra.mem_toSubmodule, htop]
    exact Algebra.mem_top
  rw [Algebra.adjoin_eq_span] at hu
  refine Submodule.span_mono (fun x hx => ?_) hu
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    exact ⟨[m], by simp⟩
  | one => exact ⟨[], by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨la, rfl⟩ := ha
    obtain ⟨lb, rfl⟩ := hb
    exact ⟨la ++ lb, by simp [List.map_append, List.prod_append]⟩

theorem iSup_indF_eq_top (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : (⨆ k, indF act k) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (indRel act) z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | tmul u v =>
    have hu := ug_mem_span_listProd p q u
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      refine Submodule.mem_iSup_of_mem l.length (Submodule.subset_span ⟨_, ?_, v, rfl⟩)
      exact Submodule.subset_span ⟨l, le_rfl, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _)]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ c ha

end GlobalTheory.InducedPBW
