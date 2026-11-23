module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransformStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_S (x : Fin 2 → ℚ) : act x ModularGroup.S = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [act, ModularGroup.S, Fin.sum_univ_two]

theorem sg_S : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x →
    sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  intro c x τ h
  obtain ⟨hc, hc6, hx⟩ := h
  set z : ℂ := (x 1 : ℂ) * (τ : ℂ) - (x 0 : ℂ) with hz
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h1 : pt x (ModularGroup.S • τ) = z / (τ : ℂ) := by
    rw [pt, UpperHalfPlane.modular_S_smul, hz]
    simp only [UpperHalfPlane.coe_mk]
    field_simp
    ring
  have h2 : pt (act x ModularGroup.S) τ = z := by
    rw [act_S, pt, hz]
    simp
    ring
  have hnot : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n := by
    intro m n heq
    apply hx
    have him := congrArg Complex.im heq
    have hre := congrArg Complex.re heq
    simp [hz, mul_sub] at him hre
    have hpos : 0 < τ.im := τ.im_pos
    have e1 : (c : ℝ) * (x 1 : ℝ) = m := by
      have : ((c : ℝ) * (x 1 : ℝ) - m) * τ.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have e0 : (c : ℝ) * (x 0 : ℝ) = ((-n : ℤ) : ℝ) := by
      rw [← mul_assoc, e1] at hre
      push_cast
      linarith
    refine ⟨⟨-n, ?_⟩, ⟨m, ?_⟩⟩
    · exact_mod_cast e0.symm
    · exact_mod_cast e1.symm
  unfold sg
  rw [h1, h2]
  exact GlobalTheory.T.smoothedThetaQProduct_modularS_transform c τ z hc hc6 hnot

end GlobalTheory.Sieg
