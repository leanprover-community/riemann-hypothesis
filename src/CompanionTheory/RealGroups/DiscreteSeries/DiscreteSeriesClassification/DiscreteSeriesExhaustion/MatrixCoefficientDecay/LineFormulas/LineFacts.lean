module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N.S

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool}

def W (A : Matrix (Fin n) (Fin n) ℂ) : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, Vm A]

def rk (A : Matrix (Fin n) (Fin n) ℂ) : ℕ := Module.finrank ℂ (Vm A)

def modA (A : Matrix (Fin n) (Fin n) ℂ) (m : Formalism.REAL.UJ ε) : ℝ≥0∞ :=
  ENNReal.ofReal (GlobalTheory.Count.layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id)

def FlagFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    1 ≤ rk A ∧ IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) ∧ rhoA A = (rk A : ℝ) * ((n : ℝ) - rk A)

def PSubEq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A → ∀ g : Formalism.REAL.UJ ε,
    g ∈ PSub ε A ↔ ∃ u ∈ flagN ε (W A), ∃ m ∈ flagM ε (W A), g = u * m

def LineFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (a : ℝ → Formalism.REAL.UJ ε) (τ : Formalism.REAL.UJ ε → ℝ), Continuous a ∧ Measurable τ ∧
      (∀ t, uMat (a t) = NormedSpace.exp ((t : ℂ) • A)) ∧ (∀ s t, a (s + t) = a s * a t) ∧
      (∀ t, a t ∈ flagM ε (W A)) ∧ (∀ t, ∀ m ∈ flagM ε (W A), m * a t = a t * m) ∧
      (∀ m ∈ flagM ε (W A), ∀ t, modA A (m * a t) = modA A m * ENNReal.ofReal (Real.exp (2 * rhoA A * t))) ∧
      (∀ u ∈ flagN ε (W A), ∀ m ∈ flagM ε (W A), ∀ t, τ (u * m * a t) = τ m + t)

def Slab : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μN μM : Measure G) [SFinite μN] [SFinite μM]
    (S : Set G) (a : ℝ → G) (δ : G → ℝ≥0∞) (τ : G → ℝ) (c : ℝ), MeasurableSet S → μM Sᶜ = 0 → Measurable a →
    Measurable δ → Measurable τ → (∀ s t, a (s + t) = a s * a t) → (∀ m ∈ S, ∀ t, m * a t ∈ S) →
    (∀ t, μM.map (· * a t) = μM) → (∀ m ∈ S, ∀ t, δ (m * a t) = δ m * ENNReal.ofReal (Real.exp (2 * c * t))) →
    (∀ m ∈ S, ∀ t, τ (m * a t) = τ m + t) → (∀ m ∈ S, δ m ≠ 0) →
    ∀ F : G → ℝ≥0∞, Measurable F → (∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN) < ⊤ →
      ∀ᵐ p ∂(μN.prod μM), (∫⁻ t in Set.Ioi (0 : ℝ), F (p.1 * p.2 * a t) * ENNReal.ofReal (Real.exp (2 * c * t))) < ⊤

def Fub : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (μN μM : Measure (Formalism.REAL.UJ ε)), SFinite μN ∧ SFinite μM ∧ μM (flagM ε (W A))ᶜ = 0 ∧
      (∀ a : Formalism.REAL.UJ ε, a ∈ flagM ε (W A) → (∀ m ∈ flagM ε (W A), m * a = a * m) → μM.map (· * a) = μM) ∧
      (∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
        (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) →
        ∫⁻ g, F g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN) ∧
      ∀ μ, IsParHaar ε A μ → ∀ E : Set (Formalism.REAL.UJ ε), MeasurableSet E →
        (μN.prod μM) {p | p.1 * p.2 ∈ E} = 0 → μ E = 0

def KMaj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    CompanionTheory.D.LK.IsKMod ε σ D E → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ → ∀ (u : D) (ξ : H),
      ∃ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F ∧ (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) ∧
        (∫⁻ g, F g ∂(Formalism.REAL.muG ε)) < ⊤ ∧ ∀ g : Formalism.REAL.UJ ε, ‖⟪ξ, σ (uMat g) u⟫_ℂ‖ₑ ^ 2 ≤ F g

def StartOf : Prop := FlagFacts → PSubEq → LineFacts → Slab → Fub → KMaj → Start

end CompanionTheory.RgExh.Dec.N.S
