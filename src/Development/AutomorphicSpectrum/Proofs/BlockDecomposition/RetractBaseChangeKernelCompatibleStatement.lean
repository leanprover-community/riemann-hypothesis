module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatible
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.retract_base_change_kernel_compatible : ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  exact @GlobalTheory.CompanionTheory.Retract.constants_of_retract
