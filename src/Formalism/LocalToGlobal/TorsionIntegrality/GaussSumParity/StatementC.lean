module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
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
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 cob UnrOK IsLawOfLog)

section Defs

variable {K : Type} [Field K]

def IsHom (F FE : MvPowerSeries (Fin 2) K) (θ : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff θ = 0 ∧
  PowerSeries.subst F θ = MvPowerSeries.subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] FE

def mulS (K : Type) [Field K] (l : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l)

end Defs

def NormRel {K : Type} [NormedField K] [CharZero K] (l : ℕ) (σ : K →+* K) (ph : PowerSeries K)
    (α : K) : Prop :=
  Simeq (PowerSeries.subst (mulS K l α) ph : MvPowerSeries Unit K)
    (MvPowerSeries.C (α * σ α) * ph)

def SigmaIsom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ a : K, ‖σ a‖ = ‖a‖

def FixedIsLimit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∀ k : ℕ, ∃ n : ℕ, ‖x - n‖ ≤ ((l : ℝ) ^ k)⁻¹

def SimeqClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : ℕ → MvPowerSeries τ K) (g : MvPowerSeries τ K),
    (∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n g))) →
    (∀ k, Simeq (f k) 0) → Simeq g 0

def SimeqFixed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (f : MvPowerSeries τ K) (c : K), ‖c‖ ≤ 1 → σ c = c →
    Simeq f 0 → Simeq (MvPowerSeries.C c * f) 0

def CoboundaryCocycleTransportAlongHom : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ = (l : ℝ)⁻¹ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ (FE : MvPowerSeries (Fin 2) K) (θ phE ph : PowerSeries K),
      MvPowerSeries.constantCoeff FE = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) → IsHom F FE θ →
      F1 FE (cob FE phE) → Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      F1 F (cob F ph)

def TransportNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (θ phE ph eE : PowerSeries K) (α : K),
      PowerSeries.constantCoeff θ = 0 → (∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) →
      PowerSeries.constantCoeff eE = 0 →
      ‖α‖ ≤ 1 → σ (σ α) = α →
      PowerSeries.subst (mulS K l α) θ = PowerSeries.subst θ eE →
      Simeq (PowerSeries.subst eE phE : MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * phE) →
      Simeq (ph : MvPowerSeries Unit K) (PowerSeries.subst θ phE) →
      NormRel l σ ph α

def NormUnits : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (ph : PowerSeries K), PowerSeries.constantCoeff ph = 0 →
    ∀ S : Set K, (∀ α ∈ S, NormRel l σ ph α) →
      ∀ α : K, (∀ ε : ℝ, 0 < ε → ∃ a ∈ S, ‖a - α‖ < ε) → NormRel l σ ph α

def SecondLevelOfNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ ph : PowerSeries K, PowerSeries.constantCoeff ph = 0 → F1 F (cob F ph) →
    (∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) →
      F2 l σ (cob F ph) ∧
      (∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → NormRel l σ ph α) ∧
      Simeq (MvPowerSeries.C (2 : K) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) (cob F ph))

def FOfBetaHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, Formalism.InvariantFactorPaths.G7.BetaHyp l F be0 → F1 F be0 ∧ F2 l σ be0

end Formalism.L2.Th1.D
