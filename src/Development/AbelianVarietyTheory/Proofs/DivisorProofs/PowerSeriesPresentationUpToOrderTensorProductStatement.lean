module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct : ∀ (k : Type) [CommRing k] (σ τ : Type) [Finite σ] [Finite τ] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : τ → B) (hy : ∀ i, IsNilpotent (y i)) (hz : ∀ i, IsNilpotent (Sum.elim (fun i => x i ⊗ₜ[k] (1 : B)) (fun j => (1 : A) ⊗ₜ[k] y j) i)), Function.Surjective (evA k x hx) → Function.Surjective (evA k y hy) → Function.Surjective (evA k _ hz) ∧ ∀ N : ℕ, (∀ f, evA k x hx f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (∀ f, evA k y hy f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ f, evA k _ hz f = 0 → ∀ α : (σ ⊕ τ) →₀ ℕ, α.degree < N → coeff α f = 0 := by
  first | exact @GlobalTheory.evA_tensor_presents | exact GlobalTheory.evA_tensor_presents | (intros; apply GlobalTheory.evA_tensor_presents <;> assumption)
