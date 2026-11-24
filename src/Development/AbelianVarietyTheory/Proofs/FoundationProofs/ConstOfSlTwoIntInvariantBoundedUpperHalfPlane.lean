module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.NumberTheory.ModularForms.Basic

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.KZ.LevelOne

theorem const_of_invariant_bounded :
    ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) →
      (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  intro φ hd hinv hb
  let f : ℍ → ℂ := fun τ => φ τ
  have hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := fun γ τ => by
    simp only [f]
    rw [← GlobalTheory.KZ.SiegelModel.mob_ofSL]
    exact hinv γ τ τ.2
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    ext τ; simpa [SL_slash_apply] using hfinv γ τ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hd.congr fun z hz => ?_
    simp only [Function.comp_apply, f]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty f := by
    obtain ⟨M, t, h⟩ := hb
    refine isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩
    exact h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
      holo' := hholo
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hs γ]
        exact hbdd }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z hz => ?_⟩
  have := congrFun hc ⟨z, hz⟩
  exact this

end GlobalTheory.KZ.LevelOne
