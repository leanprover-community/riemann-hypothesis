module

public import Lib.Speed
import TauCeti.MeasureTheory.Measure.FiberMeasure

/-!
# Measures below a fibre measure

Let `π : X → B` be a map, `μ` a measure on `X` and `ν` a measure on `B`. This file defines
`New.LeFibreMeasure` (equivalent to `TauCeti.IsLeFiberMeasure`) and records its coordinate,
invariance, two-step fibration, and pushforward rules.

## Relation to the literature

Fibre measures: Weil, Sur la formule de Siegel dans la théorie des groupes classiques, no. 6.
-/

@[expose] public section

namespace New

open MeasureTheory Measure Filter Topology Set ENNReal

variable {X X' B B' P : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace X']
  [MeasurableSpace X'] [TopologicalSpace B] [MeasurableSpace B] [TopologicalSpace B']
  [MeasurableSpace B'] [MeasurableSpace P]

/-- The measure `l` is at most the fibre measure `dμ / dν` of `π : X → B` over `b`: for every
lower semicontinuous `K ≥ 0`, a bound `∫_{π ∈ S} K dμ ≤ C ν(S)` for all open sets `S` contained
in some neighbourhood of `b` gives `∫ K dl ≤ C`. -/
def LeFibreMeasure (μ : Measure X) (ν : Measure B) (π : X → B) (b : B) (l : Measure X) : Prop :=
  ∀ K : X → ℝ≥0∞, LowerSemicontinuous K → ∀ C : ℝ≥0∞,
    (∀ᶠ S : Set B in (𝓝 b).smallSets, IsOpen S → ∫⁻ x : X in π ⁻¹' S, K x ∂μ ≤ C * ν S) →
    ∫⁻ x : X, K x ∂l ≤ C

namespace LeFibreMeasure

variable {μ μ' l l' : Measure X} {ν : Measure B} {ν' : Measure B'} {π π' : X → B} {b : B}

private theorem iff_tauCeti :
    LeFibreMeasure μ ν π b l ↔ TauCeti.IsLeFiberMeasure μ ν π b l :=
  TauCeti.isLeFiberMeasure_iff.symm

/-- Coordinate criterion for `LeFibreMeasure`: a parametrisation `ψ` with weight `w`, continuous at
`b` for almost every `p` and dominated by `μ`, yields a measure below the fibre measure over `b`. -/
theorem of_coordinates [OpensMeasurableSpace X] [OpensMeasurableSpace B] [FirstCountableTopology B]
    [ν.IsOpenPosMeasure] [IsLocallyFiniteMeasure ν] {ρ : Measure P}
    {ψ : B → P → X} {w : B → P → ℝ≥0∞} {V : Set B} (hπ : Measurable π)
    (hψ : Measurable ψ.uncurry) (hw : Measurable w.uncurry) (hV : V ∈ 𝓝 b)
    (h_fibre : ∀ t ∈ V, ∀ᵐ p : P ∂ρ, w t p ≠ 0 → π (ψ t p) = t)
    (h_cont : ∀ᵐ p : P ∂ρ, ContinuousAt (ψ · p) b ∧ ContinuousAt (w · p) b)
    (h_le : ∀ K : X → ℝ≥0∞, Measurable K →
      ∫⁻ t : B in V, ∫⁻ p : P, w t p * K (ψ t p) ∂ρ ∂ν ≤ ∫⁻ x : X, K x ∂μ) :
    LeFibreMeasure μ ν π b ((ρ.withDensity (w b)).map (ψ b)) :=
  iff_tauCeti.2 <| hπ.isLeFiberMeasure_of_coordinates (ν.finiteAt_nhds b)
    (fun _ ↦ hψ.of_uncurry_left) (fun _ ↦ hw.of_uncurry_left) hV h_fibre
    (h_cont.mono fun _ h ↦ ⟨h.1, h.2.lowerSemicontinuousAt⟩) h_le

/-- A measure-preserving map `φ : B × P → X` with `π (φ (t, p)) = t`, continuous in `t` at `b`,
pushes `ρ` forward to a measure below the fibre measure `dμ / dν` of `π` over `b`. -/
theorem of_measurePreserving [OpensMeasurableSpace X] [OpensMeasurableSpace B]
    [FirstCountableTopology B] [ν.IsOpenPosMeasure] [IsLocallyFiniteMeasure ν] {ρ : Measure P}
    [SFinite ρ] {φ : B × P → X} (hφ : MeasurePreserving φ (ν.prod ρ) μ) (hπ : Measurable π)
    (h_fibre : ∀ (t : B) (p : P), π (φ (t, p)) = t)
    (h_cont : ∀ p : P, ContinuousAt (fun t : B ↦ φ (t, p)) b) :
    LeFibreMeasure μ ν π b (ρ.map fun p : P ↦ φ (b, p)) :=
  iff_tauCeti.2 <| hφ.isLeFiberMeasure hπ (ν.finiteAt_nhds b)
    (fun t ↦ .of_forall (h_fibre t)) (.of_forall h_cont)

/-- `LeFibreMeasure` is preserved when `π` is changed on a `μ`-null set. -/
theorem congr (hl : LeFibreMeasure μ ν π b l) (hπ : π =ᵐ[μ] π') : LeFibreMeasure μ ν π' b l :=
  iff_tauCeti.2 <| (iff_tauCeti.1 hl).congr hπ

/-- `LeFibreMeasure` is preserved by a measure-preserving homeomorphism `e` of the base. -/
theorem comp_homeomorph [BorelSpace B] [BorelSpace B'] (hl : LeFibreMeasure μ ν π b l)
    (e : B ≃ₜ B') (he : MeasurePreserving e ν ν') : LeFibreMeasure μ ν' (e ∘ π) (e b) l :=
  iff_tauCeti.2 <| (iff_tauCeti.1 hl).comp_homeomorph e he

/-- Two-step fibration rule for `LeFibreMeasure` along `(π, π₂)` with `π₂` continuous. -/
theorem trans {π₂ : X → B'} {b' : B'} [SFinite ν'] [OpensMeasurableSpace X]
    (hl : LeFibreMeasure μ ν π b l) (hl' : LeFibreMeasure l ν' π₂ b' l') (hπ₂ : Continuous π₂) :
    LeFibreMeasure μ (ν.prod ν') (fun x : X ↦ (π x, π₂ x)) (b, b') l' :=
  iff_tauCeti.2 <| (iff_tauCeti.1 hl).trans (iff_tauCeti.1 hl') hπ₂

/-- Pushforward of `LeFibreMeasure` along a measurable family of continuous maps respecting `π`. -/
theorem map_prod [OpensMeasurableSpace X'] [OpensMeasurableSpace B] [FirstCountableTopology X]
    [SFinite μ] [SFinite l] {ρ : Measure P} [SFinite ρ] {φ : P × X → X'} {π₀ : X' → B}
    (hl : LeFibreMeasure μ ν π b l) (hφ : Measurable φ)
    (h_cont : ∀ p : P, Continuous fun x : X ↦ φ (p, x)) (hπ₀ : Measurable π₀)
    (h_comm : ∀ (p : P) (x : X), π₀ (φ (p, x)) = π x) :
    LeFibreMeasure ((ρ.prod μ).map φ) ν π₀ b ((ρ.prod l).map φ) :=
  iff_tauCeti.2 <| (iff_tauCeti.1 hl).map_prod hφ (.of_forall h_cont) hπ₀ h_comm

/-- Pushforward of `LeFibreMeasure` along a continuous measurable map `φ`. -/
theorem map [OpensMeasurableSpace X'] [OpensMeasurableSpace B] {φ : X → X'} {π₀ : X' → B}
    (hl : LeFibreMeasure μ ν (π₀ ∘ φ) b l) (hφ : Measurable φ) (h_cont : Continuous φ)
    (hπ₀ : Measurable π₀) : LeFibreMeasure (μ.map φ) ν π₀ b (l.map φ) :=
  iff_tauCeti.2 <| (iff_tauCeti.1 hl).map hφ h_cont hπ₀

end LeFibreMeasure

end New
