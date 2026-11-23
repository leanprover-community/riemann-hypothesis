module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMul
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det ≠ 0 → ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ, Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧ Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  exact @GlobalTheory.OddFrame.exists_tendsto_evM_mul
