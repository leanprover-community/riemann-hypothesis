module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S

def RowsDep : Prop :=
  ∀ (E : Type) [Field E] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (u : Fin r → E), u ≠ 0 →
    (∀ b, ∑ c, u c * Z (Fin.castSucc c) b = 0) → leadMinorE Z (r + 1) = 0 ∧ leadMinorE Z r = 0

def RightInv : Prop :=
  ∀ (E : Type) [Field E] (r : ℕ) (β : Matrix (Fin r) (Fin (r + 1)) E),
    (∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0) →
    ∃ (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E),
      β * Q = 1 ∧ (∀ c, ∑ b, β c b * v b = 0) ∧ ∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j

def SkewSolve : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (β x : Matrix (Fin r) (Fin (r + 1)) E)
    (Q : Matrix (Fin (r + 1)) (Fin r) E) (v l : Fin (r + 1) → E),
    (∀ u : Fin r → E, (∀ b, ∑ c, u c * β c b = 0) → u = 0) →
    β * Q = 1 → (∀ c, ∑ b, β c b * v b = 0) → (∀ i j, (Q * β) i j = (if i = j then 1 else 0) - v i * l j) →
    (∀ a b, ∑ c, (star (β c a) * x c b + star (x c a) * β c b) = 0) →
      (∀ c d, (x * Q) c d + star ((x * Q) d c) = 0) ∧ x = (x * Q) * β

end PI.TermsAtPtFiniteW
