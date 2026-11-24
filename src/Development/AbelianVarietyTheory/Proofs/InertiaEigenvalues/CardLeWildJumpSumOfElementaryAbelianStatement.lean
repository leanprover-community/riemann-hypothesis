module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
