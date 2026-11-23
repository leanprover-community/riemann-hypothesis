module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeAction
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices.CocBound

theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
