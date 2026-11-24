module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DivStable
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Order.CompletePartialOrder
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

namespace Formalism.InvariantFactorPaths.PW

open Finset

def InvInv : Prop :=
  ∀ (K W ι : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (E : ι → ι → Module.End K W), GlRel E → ∀ (l : ℕ) (NN : Submodule K W),
    (∀ a b, ∀ x ∈ NN, E a b x ∈ NN) →
    (∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0) →
    ∀ L : List ι, L.Nodup → ∀ u ∈ NN, (∀ a ∈ L, E a a u = 0) →
      (∀ a ∈ L, ∀ b ∈ L, E a b (InvOp E l L u) = 0) ∧ InvOp E l L u ∈ NN ∧
      InvOp E l L u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b)

def InvNat : Prop :=
  ∀ (K W W' ι : Type) [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
    (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W'),
    (∀ a b x, θ (E a b x) = E' a b (θ x)) → ∀ (l : ℕ) (L : List ι) (x : W),
      θ (InvOp E l L x) = InvOp E' l L (θ x)

def InvInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W ι : Type) [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
    (E : ι → ι → Module.End ℚ_[p] W), GlRel E → ∀ (M : AddSubgroup W), ZpClosed p M → DivStable E M →
    ∀ (l : ℕ) (L : List ι), L.Nodup → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p (l + L.length - 1))) • InvOp E l L u ∈ M

def HomRel : Prop :=
  ∀ (K V W ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W), GlRel EV → GlRel EW → GlRel (homAct EV EW)

def HomDiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V W ι : Type) [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
    [DecidableEq ι] (EV : ι → ι → Module.End ℚ_[p] V) (EW : ι → ι → Module.End ℚ_[p] W)
    (L : AddSubgroup V) (M : AddSubgroup W), ZpClosed p M → DivStable EV L → DivStable EW M →
      ZpClosed p (HomLat (K := ℚ_[p]) L M) ∧ DivStable (homAct EV EW) (HomLat (K := ℚ_[p]) L M)

def HomTrace : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (ψ : V →ₗ[K] V),
    ψ ∈ (⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) → LinearMap.trace K V ψ = 0

end Formalism.InvariantFactorPaths.PW
