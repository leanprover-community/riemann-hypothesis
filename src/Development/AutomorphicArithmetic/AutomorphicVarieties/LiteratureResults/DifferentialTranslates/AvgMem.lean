module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
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

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem avgMem : AvgMem := by
  intro Γ V S _ _ _ d G u hu q c
  obtain ⟨hsm, hfin, -⟩ := hu
  have hc : ∀ γ s, ContDiffOn ℝ ∞ ((c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    fun γ s => (c γ).2 s
  simp only [Geo.Om, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro s
  refine ⟨?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨N, hN, hF⟩ := hfin s p hp
    obtain ⟨O, hON, hO, hpO⟩ := mem_nhds_iff.mp hN
    refine ⟨O, hO, hpO, ?_⟩
    have hsum : ContDiffOn ℝ ∞ (fun x => ∑ γ ∈ hF.toFinset,
        u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (G.Y ∩ O) := by
      apply ContDiffOn.sum
      intro γ _
      have h1 : ContDiffOn ℝ ∞ (fun x => u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) (G.Y ∩ O) :=
        ((hsm _).comp (G.ρ γ⁻¹).contDiff.contDiffOn
          (fun x hx => G.maps γ⁻¹ x hx.1))
      exact h1.smul ((hc γ s).1.mono Set.inter_subset_left)
    refine hsum.congr ?_
    intro x hx
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hON hx.2, ?_⟩
    intro h0
    rw [Function.mem_support] at hγ
    exact hγ (by rw [h0, zero_smul])
  · intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro γ
    simp [(hc γ s).2 p hp]

end UpperTheory.V.Lit.Dr
