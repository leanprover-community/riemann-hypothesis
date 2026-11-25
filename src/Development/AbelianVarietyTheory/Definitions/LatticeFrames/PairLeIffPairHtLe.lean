module

public import Formalism.LocalRingCardinality.DataArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

def IsoAll (N A : HLat K) (e : N.V →ₗ[K] A.V) : Prop := ∀ v x, nrm A v (e x) = nrm N v x

def Norming (B M : HLat K) (pr : B.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∀ (w : B.V) (v : InfinitePlace K), ∃ z, v (pr w z) = nrm B v w ^ 2 ∧ nrm M v z = nrm B v w

def Reads (N B A M : HLat K) (Ψ : N.V →ₗ[K] B.V) (Φ : A.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∃ (e : N.V →ₗ[K] A.V) (pr : B.V →ₗ[K] Module.Dual K M.V),
    IsoAll N A e ∧ Norming B M pr ∧ ∀ x, Φ (e x) = pr (Ψ x)

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

variable {K n}

end Std

end GlobalTheory.Core.Ht2

end
