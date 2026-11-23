module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory

theorem finiteDim_functions_detected_by_finset (K : Type) (W : Submodule ℂ (K → ℂ))
    (hW : FiniteDimensional ℂ W) :
    ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  haveI := hW
  let N : Finset K → Submodule ℂ (K → ℂ) := fun s =>
    W ⊓ ⨅ k ∈ s, LinearMap.ker (LinearMap.proj k : (K → ℂ) →ₗ[ℂ] ℂ)
  have memN : ∀ s w, w ∈ N s ↔ w ∈ W ∧ ∀ k ∈ s, w k = 0 := by
    intro s w
    simp [N, Submodule.mem_iInf]
  have hex : ∃ n, ∃ s : Finset K, Module.finrank ℂ (N s) = n := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset K, Nat.find hex ≤ Module.finrank ℂ (N s) :=
    fun s => Nat.find_min' hex ⟨s, rfl⟩
  have hfin : ∀ s, FiniteDimensional ℂ (N s) := fun s =>
    Submodule.finiteDimensional_of_le (inf_le_left)
  refine ⟨s0, fun w hw hvan => ?_⟩
  have hwN : w ∈ N s0 := (memN s0 w).2 ⟨hw, hvan⟩
  funext k
  have hle : N (insert k s0) ≤ N s0 := by
    intro v hv
    rw [memN] at hv ⊢
    exact ⟨hv.1, fun j hj => hv.2 j (Finset.mem_insert_of_mem hj)⟩
  have heq : N (insert k s0) = N s0 :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hs0]; exact hmin _)
  rw [← heq, memN] at hwN
  exact hwN.2 k (Finset.mem_insert_self k s0)

end GlobalTheory
