module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPower
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → (∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂) → (∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0) → ∀ w : ℕ × ℕ → Wq l a, LTo0 l w → ∀ v b : ℕ × ℕ → Wq l a, frob2 φ₂ (ofW t K e w) = ofW t K e v → frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b → LTo0 l v ∧ LTo0 l b := by
  first | exact @GlobalTheory.CrysPrism.frob_keeps_decay | exact GlobalTheory.CrysPrism.frob_keeps_decay | (intros; apply GlobalTheory.CrysPrism.frob_keeps_decay <;> assumption)
