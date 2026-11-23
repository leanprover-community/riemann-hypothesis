module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.ComplexProjective

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.CP

noncomputable section

def PolydiscSubmean.Statement : Prop :=
  ∀ (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (f : (Fin D → ℂ) → ℂ), 0 < n → 0 < R →
    (∀ j, 0 ≤ lam j) → AnalyticOnNhd ℂ f (Metric.closedBall 0 (R / Real.sqrt n)) →
    ‖f 0‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2)

def LocalBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) → ∀ (x : X) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop, bergman W dV (V n) n x ≤ (bergmanDens W dV x + ε) * (n : ℝ) ^ D

def UniformBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V], V ≤ L.sections n →
        ∀ x : X, bergman (W₀.lerp W₁ t) dV V n x ≤ C * (n : ℝ) ^ D

def IntegralOfBergman.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∫ x, bergman W dV V n x ∂dV.μ = Module.finrank ℂ V

def L1Convergence.Statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (g : ℕ → Ω → ℝ)
    (b : Ω → ℝ) (C : ℝ), (∀ n, Integrable (g n) μ) → Integrable b μ →
    (∀ n x, 0 ≤ g n x ∧ g n x ≤ C) →
    (∀ (x : Ω) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ b x + ε) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, b x ∂μ - ε ≤ ∫ x, g n x ∂μ) →
    Tendsto (fun n => ∫ x, |g n x - b x| ∂μ) atTop (𝓝 0)

def BergmanL1Convergence.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens W dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n)) →
      Tendsto (fun n : ℕ => ∫ x, |((n : ℝ) ^ D)⁻¹ * bergman W dV (V n) n x - bergmanDens W dV x|
        ∂dV.μ) atTop (𝓝 0)

lemma lerp_self_φ {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (t : ℝ) : (W.lerp W t).φ = W.φ := by
  funext j x
  simp [Weight.lerp]

def MetricChange.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤
          Module.finrank ℂ (V n)) →
      ∀ (e : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n)) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          |chiGram W₁ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
              chiGram W₀ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
            (n : ℝ) ^ (D + 1) / 2 * ∫ t in (0 : ℝ)..1,
              ∫ x, Weight.diff W₁ W₀ x * bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ| ≤
            ε * (n : ℝ) ^ (D + 1)

def SupNormAgainstL2.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s ∈ L.sections n, ∀ x : X,
      Real.sqrt (ptNormSq W n s x) ≤ C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s)) ∧
    ∀ (n : ℕ), ∀ s ∈ L.sections n, ∀ M : ℝ, (∀ x : X, Real.sqrt (ptNormSq W n s x) ≤ M) →
      Real.sqrt (sectionL2NormSq W dV n s) ≤ M

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
