module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_dual_oddFrame_cuspForms : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0) → ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧ ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | exact GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | (intros; apply GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms <;> assumption)
