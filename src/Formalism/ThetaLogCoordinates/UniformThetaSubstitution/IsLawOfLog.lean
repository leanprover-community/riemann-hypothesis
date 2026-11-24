module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def UnrOK (K : Type) [NormedField K] (p : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ 2 < p ∧ ‖(p : K)‖ = (p : ℝ)⁻¹ ∧ (∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (p : ℝ) ^ k) ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹

section Defs

variable {K : Type} [Field K]

def cob (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst F f - at1 0 f - at1 1 f

def swap2 (H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] H

def in3 (f : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] f

def d1 (F H : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![in3 F, MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] H

def DivAB (H : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, n 0 = 0 ∨ n 1 = 0 → MvPowerSeries.coeff n H = 0

end Defs

def IsLawOfLog {K : Type} [NormedField K] (p : ℕ) (F : MvPowerSeries (Fin 2) K) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ Integral F ∧ cob F (lgF K p) = 0

def LawExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    (∃ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F) ∧
    ∀ F F' : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.constantCoeff F' = 0 → cob F (lgF K p) = 0 → cob F' (lgF K p) = 0 → F = F'

def DivDeriv : Prop :=
  ∀ (K ι κ : Type) [Finite ι] [DecidableEq ι] [NormedField K] [IsUltrametricDist K] [CharZero K]
    (p : ℕ), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ (x : ι) (Φ : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K) (Y : MvPowerSeries κ K),
      Integral (MvPowerSeries.pderiv (R := K) x Φ) →
      (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
      MvPowerSeries.constantCoeff Y = 0 → Integral Y →
      ∀ n, ‖MvPowerSeries.coeff n
        (MvPowerSeries.subst (Function.update φ x (φ x + MvPowerSeries.C (p : K) * Y)) Φ -
          MvPowerSeries.subst φ Φ)‖ ≤ (p : ℝ)⁻¹

def DeIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) (σ : K →+* K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F → Integral (cob F (g0F K p))

def DerivA : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser K p) -
      at1 0 (PowerSeries.derivative (R := K) (lgF K p)) * at1 1 (g0F K p)) ∧
    Integral (MvPowerSeries.pderiv (R := K) 0 (Aser' K p))

def LemmaOne : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ f : PowerSeries K, PowerSeries.constantCoeff f = 0 → Integral (cob F f) →
      ∃ (α β : K) (R : PowerSeries K), ‖α‖ ≤ 1 ∧ (∀ n, ‖PowerSeries.coeff n R‖ ≤ 1) ∧
        f = PowerSeries.C α * g0F K p + PowerSeries.C β * lgF K p + R

def LemmaTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ H : MvPowerSeries (Fin 2) K, DivAB H → Integral (d1 F H) → Integral (d1 F (swap2 H)) →
      ∃ (β : K) (R : MvPowerSeries (Fin 2) K), Integral R ∧
        H = MvPowerSeries.C β * (at1 0 (lgF K p) * at1 1 (lgF K p)) + R

def BetaHyp {K : Type} [NormedField K] [CharZero K] (p : ℕ) (F be : MvPowerSeries (Fin 2) K) :
    Prop :=
  DivAB be ∧ Simeq (d1 F be) 0 ∧ Simeq (d1 F (swap2 be)) 0 ∧
    ∀ ζ : K, ζ ^ (p ^ 2 - 1) = 1 →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
          MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] be)
        (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
          MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] be)

def BetaIsG : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (p : ℕ)
    (σ : K →+* K), UnrOK K p σ → (∃ ζ : K, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K, BetaHyp p F be →
      ∃ c : K, ‖c‖ ≤ 1 ∧ σ (σ c) = c ∧ Simeq be (Gser p c (σ c))

end Formalism.InvariantFactorPaths.G7
