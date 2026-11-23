module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
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


theorem _root_.GlobalTheory.T.exists_stable_graph_of_equal_annihilators : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.CommDet.stable_graph | exact GlobalTheory.CommDet.stable_graph | (intros; apply GlobalTheory.CommDet.stable_graph <;> assumption)
