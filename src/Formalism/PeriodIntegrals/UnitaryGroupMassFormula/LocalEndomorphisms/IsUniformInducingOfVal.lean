module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective
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

open NumberField IsDedekindDomain Uniformity

namespace PI.LocalEndW

theorem isUniformInducing_of_val {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (hτ : ∀ x, Valued.v (τ x) = Valued.v x) :
    IsUniformInducing τ := by
  have hb := Valued.hasBasis_uniformity (v.adicCompletion F) _
  have hτ' : ∀ y, Valued.v.restrict (τ y) = Valued.v.restrict y := fun y =>
    le_antisymm
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
  refine ⟨(hb.comap _).ext hb (fun γ _ => ⟨γ, trivial, ?_⟩) (fun γ _ => ⟨γ, trivial, ?_⟩)⟩
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rw [← map_sub, hτ']
    exact hp
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rwa [← map_sub, hτ'] at hp

theorem valContinuous : ValContinuous := fun _ _ _ _ τ hτ => (isUniformInducing_of_val τ hτ).uniformContinuous.continuous

end PI.LocalEndW
