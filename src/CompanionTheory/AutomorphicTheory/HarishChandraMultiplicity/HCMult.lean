module

public import Formalism.PeriodIntegrals.HCMult
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfFiniteRank
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.HCMult

open PI.UpqRep CompanionTheory.D.gk.admitted

theorem harish_chandra_multiplicity : PI.HCMult := by
  intro n ε H _ _ _ σ hσ hirr S hfd hS
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => unitary_group_admissible n ε H σ hσ hirr S hS (b i) (b i).2
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, hΘ, rfl⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap Θ).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hkU := Kset_sub hk
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    have hks : k.conjTranspose ∈ Kset ε := by
      refine ⟨Unitary.star_mem hk.1, ?_⟩
      have h1 : k.conjTranspose * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
      calc k.conjTranspose * Jm ε = k.conjTranspose * Jm ε * (k * k.conjTranspose) := by
            rw [hk1, Matrix.mul_one]
        _ = k.conjTranspose * (Jm ε * k) * k.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = Jm ε * k.conjTranspose := by
            rw [← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hkU)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hkU _ (Kset_sub hks), hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    obtain ⟨g, hg⟩ := exists_elt hkU
    have := hΘ ⟨g, by show toM g ∈ Kset ε; rw [hg]; exact hk⟩ (S.orthogonalProjectionOnto u)
      (S.orthogonalProjectionOnto (σ k u)) (by show _ = σ (toM g) _; rw [hg]; exact hP)
    simpa [T, toMK, hg] using this
  rintro _ ⟨v, rfl⟩

  rw [← b.sum_repr v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end CompanionTheory.HCMult
