module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

def UniqInv : Prop :=
  ∀ Λ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0 → Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ' →
    Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ' → Λ = Λ'

def LatOfDiscr : Prop :=
  ∀ Λ : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.discr Λ ≠ 0 → IsLat Λ

def ExtendEmb : Prop :=
  ∀ (M : IntermediateField ℚ ℂ), Algebra.IsAlgebraic ℚ M → ∀ ρ : M →ₐ[ℚ] ℂ,
    ∃ σ : ℂ ≃+* ℂ, ∀ x : M, σ (x : ℂ) = ρ x

def CMConjSet (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ (M : IntermediateField ℚ ℂ) [NumberField M]
    (h : jL (lamOf D cc 1) ∈ M),
    (∀ ρ : M →ₐ[ℚ] ℂ, ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ ρ ⟨jL (lamOf D cc 1), h⟩ = jL (lamOf D 𝔟 1)) ∧
    ∀ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ →
      ((Finset.univ.filter fun ρ : M →ₐ[ℚ] ℂ => ρ ⟨jL (lamOf D cc 1), h⟩ = jL (lamOf D 𝔟 1)).card : ℝ) *
        (Fintype.card (ClassGroup (𝓞 D.host.K)) : ℝ) = (Module.finrank ℚ M : ℝ)

theorem uniqInv_of_lat (hL : LatOfDiscr) (hU : Uniformization) : UniqInv := by
  intro Λ Λ' hd h2 h3
  have hd0 : Formalism.MainNotions.TaylorLogMetric.g2 Λ ^ 3 - 27 * Formalism.MainNotions.TaylorLogMetric.g3 Λ ^ 2 ≠ 0 := hd
  have hd' : Formalism.MainNotions.TaylorLogMetric.discr Λ' ≠ 0 := by
    unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [← h2, ← h3]
    exact hd0
  exact (hU _ _ hd0).2 Λ Λ' (hL Λ hd) (hL Λ' hd') rfl rfl h2.symm h3.symm

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
