module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem aux {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μG : Measure G) (H H' : Subgroup G) (e : H' = H)
    (μ : Measure H) (hμ : μ.IsHaarMeasure) : ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser H' μ' ρ ↔ IsQuotNormaliser H μ ρ) ∧ ∀ F, quotIntegral μG H' μ' F = quotIntegral μG H μ F := by
  subst e
  exact ⟨μ, hμ, fun _ => Iff.rfl, fun _ => rfl⟩

theorem UpperTheory.V.Z.Tf.Orb.untwist :
    UpperTheory.V.Z.Tf.Orb.Untwist := by
  intro k _ _ _ _ n _ _ μk γ
  have h1 : ∀ g : GL (Fin n) k, sigmaGL (1 : k ≃ₐ[k] k) g = g := fun g => by rw [sigmaGL_one]; rfl
  refine ⟨fun τ => ?_, h1, fun h => ?_, fun μ hμ => ?_⟩
  · have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  · have : normGL (1 : k ≃ₐ[k] k) γ = γ := by
      rw [normGL, Module.finrank_self]
      simp [twNorm]
    rwa [IsTwRegSemisimple, this]
  · have e : twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ = Subgroup.centralizer {γ} := by
      ext x
      rw [mem_twCent, h1, Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
      rw [commute_iff_eq]
    obtain ⟨μ', a, b, c⟩ := aux μk _ _ e μ hμ
    refine ⟨μ', a, b, fun f => ?_⟩
    rw [twOrbIntegralC, orbIntegralC, c]
    simp only [twConj, h1]
