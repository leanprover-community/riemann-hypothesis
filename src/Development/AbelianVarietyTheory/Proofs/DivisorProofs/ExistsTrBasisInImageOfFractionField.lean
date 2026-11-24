module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_trBasis_lift : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  intro K κ _ _ inst k R π hfrac ⟨z, hz⟩
  have hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u := by
    intro u
    have : (algebraMap ℂ κ).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [this]
  have hz' := (hiff z).1 hz
  have htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨a, b, hb, e⟩ := hfrac f
    have : f = π a / π b := by rw [← e, mul_div_cancel_right₀ _ hb]
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ :=
    ⟨fun f => isAlgebraic_algebraMap
      (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)
  have hc : Cardinal.mk (Fin k) = Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  choose J hJ using fun i : Fin k => ht (e i).2
  refine ⟨J, (hiff _).2 ?_⟩
  have := (isTranscendenceBasis_equiv e).2 hb
  convert this using 1
  funext i
  exact hJ i

end GlobalTheory.GraphLocal
