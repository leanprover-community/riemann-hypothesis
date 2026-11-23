module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalRingCardinality.Params

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : (ι → M) →ₘₗ[K] N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : (ι → MvPolynomial (Fin n × Fin n) K) →ₘₗ[K]
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
