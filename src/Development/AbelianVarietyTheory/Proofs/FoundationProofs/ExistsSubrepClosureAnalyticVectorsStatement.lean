module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_subrep_closure_analytic_vectors : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  first | exact @GlobalTheory.AnalyticClosure.exists_subrep_closure | exact GlobalTheory.AnalyticClosure.exists_subrep_closure | (intros; apply GlobalTheory.AnalyticClosure.exists_subrep_closure <;> assumption)
