module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecomposition
public import Mathlib.MeasureTheory.Group.FundamentalDomain
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

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem unf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ Γ' _ hle 𝓕 h𝓕 Q r hr hu
  let ρ : Q → Γ := fun q => ⟨r q, hr q⟩
  have key : ∀ (g g' : Γ') q q', g * r q = g' * r q' → q = q' := fun g g' q q' e =>
    (hu _ (Γ.mul_mem (hle g.2) (hr q))).unique (by simp) (by rw [e]; simp)
  have hinj : Function.Injective ρ := fun q q' e => key 1 1 q q' (congrArg (fun x : Γ => ((1 : Γ') : G) * x) e)
  have := hinj.countable
  have hn : ∀ q, NullMeasurableSet (ρ q • 𝓕) μ := fun q => h𝓕.nullMeasurableSet_smul _
  refine ⟨⋃ q, ρ q • 𝓕, ⟨NullMeasurableSet.iUnion hn, h𝓕.ae_covers.mono fun x ⟨γ, hγ⟩ => ?_, fun g g' hne => ?_⟩,
    fun f hf => ?_⟩
  · obtain ⟨q, hq, -⟩ := hu _ γ⁻¹.2
    refine ⟨⟨_, hq⟩⁻¹, Set.mem_iUnion.2 ⟨q, _, hγ, ?_⟩⟩
    simp [ρ, Subgroup.smul_def, mul_assoc]
  · have e : ∀ (g : Γ') q, g • ρ q • 𝓕 = (⟨g * r q, Γ.mul_mem (hle g.2) (hr q)⟩ : Γ) • 𝓕 := fun g q =>
      smul_smul (g : G) (r q) 𝓕
    simp only [Function.onFun, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff, e]
    refine fun q q' => h𝓕.aedisjoint fun h => hne ?_
    have h1 := congrArg Subtype.val h
    obtain rfl := key _ _ _ _ h1
    exact Subtype.ext (mul_right_cancel h1)
  · rw [lintegral_iUnion₀ hn (h𝓕.aedisjoint.comp_of_injective hinj),
      lintegral_tsum (f := fun q h => f (r q * h)) fun q => (hf.comp (measurable_const_mul (r q))).aemeasurable]
    exact tsum_congr fun q => (measurePreserving_mul_left μ (r q)).setLIntegral_comp_emb
      (measurableEmbedding_mulLeft _) f 𝓕

theorem nuabs : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  apply GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant

end PositivityTheory.PlacePermOperatorBicommutantSpan
