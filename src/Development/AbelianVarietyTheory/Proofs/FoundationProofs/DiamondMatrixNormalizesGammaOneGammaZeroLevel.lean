module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
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
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem diam_conj_mem (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  apply GlobalTheory.HeckeFamilyMatrices.CosetReps.diam_conj <;> assumption

theorem diam_normalises_lev : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  intro N l d σ hσ γ
  refine ⟨⟨σ * (γ : SL(2, ℤ)) * σ⁻¹, diam_conj_mem N l d σ hσ γ γ.2⟩, ?_⟩
  simp only [mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end GlobalTheory.HeckeFamilyMatrices
