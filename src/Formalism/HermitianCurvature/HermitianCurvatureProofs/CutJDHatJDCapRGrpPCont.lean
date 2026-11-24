module

public import Formalism.HermitianCurvature.StatementQ
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdU

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdU (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f + pOp ⟨r - 1, by omega⟩ f else ciOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdU r Y (m + 1) b f + pOp ⟨r - (m + 2), by omega⟩ (tdU r Y (m + 1) b f) -
          cOp ⟨r - (m + 1), by omega⟩ (ciOp ⟨r - (m + 2), by omega⟩ (tdU r Y m b f))
      else fun _ => 0

end tdU

def JDRCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdU r Y r b f c = Q.cmp (Q.vAB r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
