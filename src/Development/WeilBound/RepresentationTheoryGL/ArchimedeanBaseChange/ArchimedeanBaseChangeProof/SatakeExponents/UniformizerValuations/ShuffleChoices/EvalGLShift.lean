module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finsupp.SMul

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.BcB.F.F5

theorem evalGL_shift {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (y : Fin n → ℤ) (ξ : Fin n → ℂˣ) :
    evalGL (c.mapDomain (· + y)) ξ = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) * evalGL c ξ := by
  unfold evalGL
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring

theorem evalGL_sub {n : ℕ} (c d : (Fin n → ℤ) →₀ ℂ) (p q : ℂ) (ξ : Fin n → ℂˣ) :
    evalGL (p • c - q • d) ξ = p * evalGL c ξ - q * evalGL d ξ := by
  unfold evalGL
  rw [Finsupp.sum_sub_index (by intros; ring), Finsupp.sum_smul_index (by simp), Finsupp.sum_smul_index (by simp),
    Finsupp.mul_sum, Finsupp.mul_sum]
  simp [mul_assoc]

theorem peakCone : PeakCone := by
  classical
  intro n M α S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have hx0 : (fun i : Fin n => |M| * ((n : ℤ) - (i : ℕ))) ∈ coneGL n M := by
      intro i j hij
      have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
      have := le_abs_self M
      have := abs_nonneg M
      nlinarith
    refine ⟨Finsupp.single (fun i : Fin n => |M| * ((n : ℤ) - (i : ℕ)))
      (((∏ i, α i ^ (|M| * ((n : ℤ) - (i : ℕ))) : ℂˣ)⁻¹ : ℂˣ) : ℂ), ?_, ?_, by simp⟩
    · intro z hz
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hz)]
      exact hx0
    · unfold evalGL
      rw [Finsupp.sum_single_index (by simp)]
      exact Units.inv_mul _
  | insert β S hβ ih =>
    intro hα
    simp only [Finset.mem_insert, not_or] at hα
    obtain ⟨c, hc, h1, h0⟩ := ih hα.2
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ coneGL n 0, (∏ i, α i ^ y i : ℂˣ) ≠ ∏ i, β i ^ y i := by
      by_contra hcon
      push Not at hcon
      apply hα.1
      funext k
      have h0' := hcon (fun i : Fin n => (n : ℤ) - (i : ℕ)) (fun i j hij => by
        have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
        simp only
        omega)
      have h1' := hcon ((fun i : Fin n => (n : ℤ) - (i : ℕ)) + Pi.single k 1) (fun i j hij => by
        have : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
        simp only [Pi.add_apply, Pi.single_apply]
        split_ifs <;> omega)
      simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, h0', mul_right_inj] at h1'
      have h2 : α k = β k := by simpa [Pi.single_apply, apply_ite, Finset.prod_ite_eq'] using h1'
      exact h2
    have hab : ((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ) ≠ 0 :=
      sub_ne_zero.2 fun e => hne (Units.ext e)
    refine ⟨(((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ))⁻¹ • c.mapDomain (· + y) -
      ((((∏ i, α i ^ y i : ℂˣ) : ℂ) - ((∏ i, β i ^ y i : ℂˣ) : ℂ))⁻¹ * ((∏ i, β i ^ y i : ℂˣ) : ℂ)) • c,
      ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.support_smul h))
        intro i j hij
        have e1 := hc hu i j hij
        have e2 := hy i j hij
        simp only [Pi.add_apply]
        omega
      · exact hc (Finsupp.support_smul h)
    · rw [evalGL_sub, evalGL_shift, h1, mul_one, mul_one, ← mul_sub, inv_mul_cancel₀ hab]
    · intro γ hγ
      rw [evalGL_sub, evalGL_shift]
      rcases Finset.mem_insert.1 hγ with rfl | h
      · ring
      · simp [h0 γ h]

end PositivityTheory.Rg.BcB.F.F5

end
