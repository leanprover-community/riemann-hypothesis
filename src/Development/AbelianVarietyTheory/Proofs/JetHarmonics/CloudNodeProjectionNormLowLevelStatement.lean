module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.cloudNode_projection_norm_lowLevel : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.cloud_node_projection_norm | exact GlobalTheory.cloud_node_projection_norm | (intros; apply GlobalTheory.cloud_node_projection_norm <;> assumption)
