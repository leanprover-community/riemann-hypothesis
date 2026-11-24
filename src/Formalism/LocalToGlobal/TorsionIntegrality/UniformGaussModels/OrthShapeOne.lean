module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

def PhMap : Prop :=
  ∀ (K K' : Type) [Field K] [Field K'] [CharZero K] [CharZero K'] (φ : K →+* K') (l : ℕ), 2 ≤ l →
    ∀ g2 g3 s2 ε : K,
      PowerSeries.map φ (phFF l g2 g3 s2 ε) = phFF l (φ g2) (φ g3) (φ s2) (φ ε)

def CalcC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ ≤ 1 → σ (σ α) = α →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l]) ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l])) ∧
    (∀ z : MaximalUnramifiedExtension l, ‖z‖ ≤ 1 → σ z = z → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[l]) (z : ℂ_[l]))

end Formalism.L2.Th1.Top
