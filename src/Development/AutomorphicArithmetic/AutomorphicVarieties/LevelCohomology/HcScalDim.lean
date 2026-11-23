module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.scalDim :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k Γ M) (γ χ : Γ →* kˣ), (∀ g m, ρ g m = (γ g : k) • m) → (∀ σ, γ σ = 1 → finrank k (LinearMap.ker (ρ σ - 1)) = finrank k M) ∧ (∀ σ, (finrank k M = 0 ∨ γ σ ≠ 1) → finrank k (LinearMap.ker (ρ σ - 1)) = 0) ∧ ((finrank k M = 0 ∨ ∃ g, γ g ≠ χ g) → finrank k (Loc.H0dual χ ρ) = 0) := by
  intro k Γ M _ _ _ _ _ ρ γ χ h
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun hσ => ?_⟩
  · have : LinearMap.ker (ρ σ - 1) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      simp [h, hσ]
    rw [this, finrank_top]
  · have : LinearMap.ker (ρ σ - 1) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      rw [Submodule.mem_bot]
      rcases hσ with h0 | h0
      · exact (finrank_zero_iff_forall_zero.mp h0) m
      · have h1 : ((γ σ : k) - 1) • m = 0 := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, h] at hm
          rw [sub_smul, one_smul]
          exact hm
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact absurd (Units.ext (sub_eq_zero.mp h2)) h0
        · exact h2
    rw [this, finrank_bot]
  · have : Loc.H0dual χ ρ = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_bot]
      ext m
      rcases hσ with h0 | ⟨g, hg⟩
      · rw [(finrank_zero_iff_forall_zero.mp h0) m]; simp
      · have h1 := hf g m
        rw [h, map_smul, smul_eq_mul] at h1
        have h2 : ((γ g : k) - χ g) * f m = 0 := by
          rw [sub_mul, h1]; simp
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Units.ext (sub_eq_zero.mp h3)) hg
        · simpa using h3
    rw [this, finrank_bot]
