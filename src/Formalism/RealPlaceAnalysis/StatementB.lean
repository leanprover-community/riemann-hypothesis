module

public import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

def epow {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0 => fun a b => if a = b then 1 else 0
  | k + 1 => fun a b => ∑ c, epow E k a c * E c b

def etr {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ a, epow E k a a

def IsHW {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) : Prop :=
  (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0

def lsh {n : ℕ} (ν : Fin n → ℂ) : Fin n → ℂ := fun a => ν a + ((n : ℂ) - 1 - (a : ℂ))

def Amat {n : ℕ} (l : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a = b then l a else if a < b then -1 else 0

def vand {n : ℕ} (l : Fin n → ℂ) : ℂ :=
  ∏ a, ∏ b ∈ univ.filter (fun b => a < b), (l a - l b)

def EpowCov : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0)

def EtrCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (c d : Fin n), etr E k * E c d = E c d * etr E k

def HWDiag : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ (k : ℕ) (a : Fin n),
      epow E (k + 1) a a v =
        lsh ν a • epow E k a a v - ∑ b ∈ univ.filter (fun b => a < b), epow E k b b v

def DiagChar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ a : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a a v = 0

end Formalism.REAL
