module

public import Formalism.PeriodIntegrals.QuotProdK
public import Mathlib.MeasureTheory.Measure.WithDensity
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

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QPK

def InvOn {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (K : Set G) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Kᶜ = 0 ∧ ∀ s ∈ K, μ.map (fun x => s * x) = μ

def IsGrp {G : Type} [Group G] (K : Set G) : Prop :=
  (1 : G) ∈ K ∧ (∀ a ∈ K, ∀ b ∈ K, a * b ∈ K) ∧ ∀ a ∈ K, a⁻¹ ∈ K

def PosOn {G : Type} [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (K : Set G) : Prop :=
  ∀ U : Set G, IsOpen U → (U ∩ K).Nonempty → μ U ≠ 0

def mulMap {G : Type} [Group G] [MeasurableSpace G] (μ ν : Measure G) : Measure G :=
  (μ.prod ν).map (fun p => p.1 * p.2)

def prodSet {G : Type} [Group G] (N H : Set G) : Set G :=
  {s | ∃ m ∈ N, ∃ h ∈ H, s = m * h}

def HaarUniq : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Set G),
    IsClosed K → IsGrp K → ∀ μ ν : Measure G, InvOn μ K → InvOn ν K →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν

def HaarExist : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Set G),
    IsClosed K → IsGrp K →
      ∃ ν : Measure G, InvOn ν K ∧ IsFiniteMeasureOnCompacts ν ∧ PosOn ν K

def ConjInv : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N H : Set G),
    IsClosed N → IsCompact H → IsGrp N → IsGrp H → (∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) →
    ∀ μ : Measure G, InvOn μ N → IsFiniteMeasureOnCompacts μ → PosOn μ N →
      ∀ h ∈ H, μ.map (fun x => h * x * h⁻¹) = μ

def SMeas : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N H : Set G),
    IsClosed N → IsCompact H → IsGrp N → IsGrp H → (∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) →
    (∀ μ : Measure G, SigmaFinite μ → μ ≠ 0 → μ Nᶜ = 0 →
      (∀ s ∈ N, μ.map (fun x => s * x) = μ) → ∀ s ∈ N, μ.map (fun x => x * s) = μ) →
    ∀ μN μH : Measure G, InvOn μN N → IsFiniteMeasureOnCompacts μN → PosOn μN N →
      InvOn μH H → IsFiniteMeasureOnCompacts μH → PosOn μH H →
      (∀ h ∈ H, μN.map (fun x => h * x * h⁻¹) = μN) →
      InvOn (mulMap μN μH) (prodSet N H) ∧ IsFiniteMeasureOnCompacts (mulMap μN μH) ∧
        PosOn (mulMap μN μH) (prodSet N H) ∧
        (∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => x * s) = mulMap μN μH) ∧
        (mulMap μN μH).map (fun x => x⁻¹) = mulMap μN μH

def Bruhat : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (S : Set G),
    IsClosed S → IsGrp S → ∀ μ : Measure G, InvOn μ S → IsFiniteMeasureOnCompacts μ → PosOn μ S →
      (∀ s ∈ S, μ.map (fun x => x * s) = μ) →
      ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ x, ∫⁻ s, β (s * x) ∂μ = 1

def LocWeil : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (muG : Measure G) [muG.IsHaarMeasure] (μ : Measure G), SigmaFinite μ →
    μ.map (fun x => x⁻¹) = μ → ∀ β : G → ℝ≥0∞, Measurable β → (∀ x, ∫⁻ s, β (s * x) ∂μ = 1) →
      ∀ F : G → ℝ≥0∞, Measurable F →
        ∫⁻ x, F x ∂muG = ∫⁻ x, (∫⁻ s, F (s * x) ∂μ) ∂(muG.withDensity β)

def LocPack : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (muG : Measure G) [muG.IsHaarMeasure] (N H : Set G),
    IsClosed N → IsCompact H → IsGrp N → IsGrp H → (∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) →
    (∀ μ : Measure G, SigmaFinite μ → μ ≠ 0 → μ Nᶜ = 0 →
      (∀ s ∈ N, μ.map (fun x => s * x) = μ) → ∀ s ∈ N, μ.map (fun x => x * s) = μ) →
    ∃ (μN μH : Measure G) (β : G → ℝ≥0∞), InvOn μN N ∧ InvOn μH H ∧
      InvOn (mulMap μN μH) (prodSet N H) ∧ Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(mulMap μN μH) = 1) ∧
      ∀ F : G → ℝ≥0∞, Measurable F →
        ∫⁻ x, F x ∂muG = ∫⁻ x, (∫⁻ s, F (s * x) ∂(mulMap μN μH)) ∂(muG.withDensity β)

def GlobAsm : Prop := HaarUniq → LocPack → PI.QuotProdK.QuotProdK

end QPK
