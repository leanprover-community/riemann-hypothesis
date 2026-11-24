module

public import Formalism.SatakeDualWeyl.StatementF
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

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x : Matrix (Fin n') (Fin n) L) :
    Matrix (Fin n) (Fin n') L :=
  ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L)

def HomA (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) ∧
    ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ (adj σ JS JT x *ᵥ w)) i ∈ Formalism.UG.intL L

def GramEq (σ : L →+* L) {n n' : ℕ} (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  ∀ m m' : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → (∀ i, m' i ∈ Formalism.UG.intL L) → ∀ c ∈ Formalism.UG.intL L,
    (∀ i, (x *ᵥ (c • m)) i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • m')) i ∈ Formalism.UG.intL L) →
      c * (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ m) (y *ᵥ m') -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ m) (x *ᵥ m')) ∈ Formalism.UG.intL L

def SelfDual (σ : L →+* L) {n : ℕ} (JS : GL (Fin n) L) (a : GL (Fin n) L) : Prop :=
  (∀ i j, (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) i j ∈
      Formalism.UG.intL L) ∧
    ∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L

end GlobalTheory.Hk3.HoweG

end
