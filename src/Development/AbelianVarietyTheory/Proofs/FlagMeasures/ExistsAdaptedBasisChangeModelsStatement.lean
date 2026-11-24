module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.exists_adapted_basis_change_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  first | exact @GlobalTheory.AdaptedMove.adapted_move | exact GlobalTheory.AdaptedMove.adapted_move | (intros; apply GlobalTheory.AdaptedMove.adapted_move <;> assumption)
