module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
