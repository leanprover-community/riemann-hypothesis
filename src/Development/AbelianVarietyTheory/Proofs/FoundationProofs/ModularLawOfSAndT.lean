module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
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
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_one_gen (x : Fin 2 → ℚ) : act x 1 = x := by
  funext i
  fin_cases i <;> simp [act, Fin.sum_univ_two]

theorem act_mul_gen (x : Fin 2 → ℚ) (γ δ : SL(2, ℤ)) : act x (γ * δ) = act (act x γ) δ := by
  funext i
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem modular_law_of_generators (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ)
    (hP : ∀ x γ, P x → P (act x γ))
    (hS : ∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ)
    (hT : ∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) :
    ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ}
      one_mem' := by
        intro x τ _
        simp [act_one_gen]
      mul_mem' := by
        intro γ δ hγ hδ x τ hx
        rw [mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]
      inv_mem' := by
        intro γ hγ x τ hx
        have h := hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)
        rw [smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen] at h
        exact h.symm }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  intro γ
  have : γ ∈ H := hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)
  exact this

end GlobalTheory.Sieg
