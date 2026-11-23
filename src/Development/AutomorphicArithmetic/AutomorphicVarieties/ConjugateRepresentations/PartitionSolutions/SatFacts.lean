module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satFacts :
    SatFacts := by
  intro Γ V S _ _ _ d G T K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ s p
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ, t, ht, ?_, ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hT
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact hK
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ⁻¹, t, ht, ?_, ?_⟩
      · rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hT
      · rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hK
  · intro hK s
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨γ, t, ht, hT, hp⟩
    have hc : Continuous fun q : V => t • (G.ρ γ) q :=
      continuous_const.smul (G.ρ γ).continuous
    filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq
    exact ⟨γ, t, ht, hT, hq⟩
  · rintro K' hKK' s p ⟨γ, t, ht, hT, hp⟩
    exact ⟨γ, t, ht, hT, hKK' hp⟩
  · intro s p t ht
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]
    constructor
    · rintro ⟨γ, u, hu, hT, hK⟩
      exact ⟨γ, u * t, mul_pos hu ht, hT, hK⟩
    · rintro ⟨γ, u, hu, hT, hK⟩
      refine ⟨γ, u / t, div_pos hu ht, hT, ?_⟩
      rwa [div_mul_cancel₀ u ht.ne']
