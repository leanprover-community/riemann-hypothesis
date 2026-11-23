module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselSideBound
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hf : AEStronglyMeasurable f μ) (hc : 0 ≤ c) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c :=
  _root_.GlobalTheory.eLpNorm_two_of_lintegral_sq f c hc hf h

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ :=
  _root_.GlobalTheory.integral_inner_of_isometric S Φ hm hn hadd hsmul

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ :=
  fun h1 k r ε mu R Wp [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] z π u μW μN μG νq Bm h2 =>
    _root_.GlobalTheory.isoBessel_polarised h1 k r ε mu R Wp z π u μW μN μG νq Bm (GlobalTheory.isDS_of_isDG h2)

end GlobalTheory
