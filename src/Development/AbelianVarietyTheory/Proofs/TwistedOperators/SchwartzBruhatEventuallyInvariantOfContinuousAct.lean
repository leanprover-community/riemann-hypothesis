module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
