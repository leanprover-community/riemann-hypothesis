module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.FormalGroup.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace JetMomFound

section FG

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![mulN F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries

def IsIsoGm (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ IsUnit (coeff 1 f) ∧
    PowerSeries.subst F.toPowerSeries f =
      (FormalGroup.𝔾ₘ : FormalGroup R).toPowerSeries.subst
        ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]

end FG

section Padic

variable {p : ℕ} [Fact p.Prime]

def CoeffFinite (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ∃ L : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] L ∧
    ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[p]) : ℂ_[p]) ∈ L

def HtOne (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ‖((coeff p (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 ∧ ∀ k < p, ‖((coeff k (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1

end Padic

def HtOneIsGm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]), CoeffFinite F → HtOne F → ∃ f : PowerSeries 𝓞_ℂ_[p], IsIsoGm F f

end JetMomFound
