module

public import Formalism.YangianSpanCharacter.StatementT
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.YangianSpanCharacter.Y

open Matrix Formalism.YangianSpanCharacter.T

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

def lf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 1 0

def mf (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u : 𝕜) : A := τinv u * t u 0 1

def hf (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (u : 𝕜) : A := q u • (τinv u * τinv (u + 1))

def eta (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (lf t τinv u - lf t τinv v)

def mu (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (u v : 𝕜) : A :=
  (u - v)⁻¹ • (mf t τinv u - mf t τinv v)

def ModHyp (t : 𝕜 → Matrix (Fin 2) (Fin 2) A) (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜) : Prop :=
  (∀ (u v : 𝕜) (i j k l : Fin 2),
      (u - v) • (t u i j * t v k l - t v k l * t u i j) = t u k j * t v i l - t v k j * t u i l) ∧
    (∀ Y : 𝕜, (t (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J A * t Y = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ Y : 𝕜, t Y * Formalism.YangianSpanCharacter.T.J A * (t (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J A) ∧
    (∀ u ∈ S, t u 1 1 * τinv u = 1 ∧ τinv u * t u 1 1 = 1) ∧
    (∀ u v : 𝕜, Commute (t u 1 1) (t v 1 1)) ∧
    (∀ u v : 𝕜, Commute (t u 1 0) (t v 1 0))

def Y1 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * lf t τinv v - lf t τinv v * t u 1 1 = -(t u 1 1 * eta t τinv u v)

def Y1' : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → v ∈ S → u ≠ v →
      t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v

def Y3 : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ u v : 𝕜, u ∈ S → u + 1 ∈ S → u - 1 ∈ S → v ∈ S → v + 1 ∈ S → u ≠ v →
      (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
        hf τinv q v - hf τinv q (u - 1)

end Formalism.YangianSpanCharacter.Y
