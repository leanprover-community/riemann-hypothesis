module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariant
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


theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap (RingHom.id ℂ) H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap (RingHom.id ℂ) H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
