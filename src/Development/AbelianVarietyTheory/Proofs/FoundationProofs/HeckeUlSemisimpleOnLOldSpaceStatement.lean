module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSemisimpleOnLOldSpace
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeUl_semisimple_on_lOldSpace : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) →
  ∀ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) →
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) →
    (∃ g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₁) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₂) ∧
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = ⇑g₁ + ⇑g₂ ∣[(k : ℤ)] toGL (dg l 1)) ∧
    ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = 0 →
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = α • (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) := by
  exact @GlobalTheory.OldSpace.ul_oldSpace
