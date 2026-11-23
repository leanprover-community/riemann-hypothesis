module

public import Mathlib.MeasureTheory.Group.Measure
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
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
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }

theorem exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _
  have hclosed : IsClosed ((ι.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]; exact hι.isClosed_range
  let e : G₁ ≃ₜ* ι.range := closedEmbeddingRangeEquiv ι hι
  haveI : IsFiniteMeasureOnCompacts μ₁.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI : μ₁.inv.IsOpenPosMeasure :=
    ⟨fun U hU hne => by
      rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μ₁ hne.inv⟩
  haveI hinv : μ₁.inv.IsHaarMeasure := {}
  have hν : (μ₁.inv.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e
  obtain ⟨β, hβ, hmass⟩ := PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν
  refine ⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩
  have hem : Measurable e := e.continuous.measurable
  have hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G)) :=
    hβ.comp (measurable_const.mul measurable_subtype_coe)
  have h1 := hmass g⁻¹
  have hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G)) := hf.comp hem
  rw [lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv] at h1
  refine Eq.trans (lintegral_congr fun u => ?_) h1
  have : ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹ := by
    show ι u⁻¹ = _
    exact map_inv ι u
  show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))
  rw [this, mul_inv_rev]

end GlobalTheory.CompanionTheory.SW
