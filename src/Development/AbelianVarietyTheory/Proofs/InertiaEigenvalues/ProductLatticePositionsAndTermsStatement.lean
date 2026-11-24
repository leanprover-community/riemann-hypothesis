module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTerms
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.latticeTerm_prod_eq_mul_components : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.pos_term_prod | exact GlobalTheory.UnitLemma.Desc.pos_term_prod | (intros; apply GlobalTheory.UnitLemma.Desc.pos_term_prod <;> assumption)
