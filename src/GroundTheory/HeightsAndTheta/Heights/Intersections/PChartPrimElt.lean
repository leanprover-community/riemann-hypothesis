module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartPrimElt
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
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

theorem ChartPrimElt.proof : ChartPrimElt.Statement := by
  intro Φ _ _ Φ' _ _ Q _ r hfin
  set L := IntermediateField.adjoin Φ (Set.range r) with hL
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Φ L
  have hint : IsIntegral Φ α := IsIntegral.of_finite Φ α
  have hmemL : ∀ q, r q ∈ L := fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
  have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
    rintro _ ⟨q, rfl⟩
    exact (IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1
      (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact α.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨τ, hτ0⟩ := hmem
  have hτ : MvPolynomial.aeval r τ = (α : Φ') := hτ0
  have hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α := by
    rw [hτ]
    exact minpoly.algHom_eq L.val Subtype.val_injective α
  have hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L) := by
    intro q
    have h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨p, hp⟩ := h1
    exact ⟨p, hp⟩
  choose g hg using hg
  have hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q := by
    intro q
    rw [hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]
    rfl
  have hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ)) := by
    rw [hm]
    exact minpoly.irreducible hint
  refine ⟨τ, g, ?_⟩
  have hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ))
      (derivative (minpoly Φ (MvPolynomial.aeval r τ))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩
  · rw [hm]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα
  · apply minpoly.dvd
    have hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r := funext hgθ
    rw [map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]
  · intro q hq
    have hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q := by
      rintro ⟨c, hc⟩
      apply hq
      rw [← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]
    obtain ⟨a', b', hab'⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    exact ⟨b', ⟨-a', by linear_combination hab'⟩⟩

end GroundTheory.Heights₂.Heights.Inter
