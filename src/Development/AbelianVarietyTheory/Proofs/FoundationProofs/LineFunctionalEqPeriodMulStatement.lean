module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineFunctionalEqPeriodMul
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


theorem _root_.GlobalTheory.T.line_functional_eq_period_mul_alt : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  first | exact @GlobalTheory.line_functional_eq_period_mul | exact GlobalTheory.line_functional_eq_period_mul | (intros; apply GlobalTheory.line_functional_eq_period_mul <;> assumption)
