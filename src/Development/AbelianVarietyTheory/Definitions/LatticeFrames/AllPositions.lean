module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

namespace SymData

def SupportAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    h ∈ stabLat ((S.T t).bas (j + 1) c (by omega)) → ∀ x₀ e,
      (S.T t).Phi j c H ((h⁻¹).val * affPt p x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def ClassAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ stabLat ((S.T t).bas (j + 1) c (by omega)), h = r * u

def OneIndexAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u

def ExchangeAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → p ≤ S.ρ + 1 → ∃ C : ℝ, 0 < C ∧
    opE S.ψ ν p ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν 1 ((S.T t).Phi j c H)

end SymData

def AllPositions : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν ∧ S.ExchangeAt t ν

end GlobalTheory.SymChain
