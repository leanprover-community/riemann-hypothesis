module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
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

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]

    simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
