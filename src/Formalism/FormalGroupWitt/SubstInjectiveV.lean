module

public import Formalism.FormalGroupWitt.Statement
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
import Formalism.TorsionNormIteration.InvIntegralOfClass

@[expose] public section

noncomputable section

open PowerSeries

universe u v w

namespace Formalism.FG

open Formalism.G Formalism.LT

def SolveExistsV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (G : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ j, MvPowerSeries.constantCoeff (G j) = 0) →
      ∃ h : ι → MvPowerSeries τ R, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) ∧
        ∀ j, MvPowerSeries.subst h (f j) = G j

def SubstInjectiveV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, MvPowerSeries.constantCoeff (b i) = 0) →
    (∀ j, MvPowerSeries.subst a (f j) = MvPowerSeries.subst b (f j)) → a = b

def CoeffBoundV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ (τ : Type w) (f : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
      ∀ j (n : τ →₀ ℕ), ∃ k : ℕ, (∀ i, q ^ k ∣ n i) ∧
        ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1

def IntegralSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι] (τ : Type w)
    (g : MvPowerSeries ι K) (a : ι → MvPowerSeries τ K),
    IntegralMv g → (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, IntegralMv (a i)) →
      IntegralMv (MvPowerSeries.subst a g)

def FunEqSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) (α : ι → MvPowerSeries τ K), (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      (∀ i, IntegralMv (α i)) →
      IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst α (f j))

def LowCoeffV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K),
    2 ≤ q → ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K) (τ : Type w)
    (D : ι → MvPowerSeries τ K), IsFunEqTypeV p q hq σ M D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1

def InvIntegralV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K),
    IsIdMod2 f →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j))) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1) →
    ∀ h : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) →
      C (fun j => MvPowerSeries.subst h (f j)) → ∀ i, IntegralMv (h i)

def FrobLiftPadicSq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], FunctionalEquationSetting ℚ_[l] l (l ^ 2) (RingHom.id ℚ_[l])

end Formalism.FG
