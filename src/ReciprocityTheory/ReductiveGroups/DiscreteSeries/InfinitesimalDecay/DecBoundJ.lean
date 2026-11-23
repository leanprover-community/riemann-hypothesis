module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

def wAct {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → Module.End ℂ M
  | [] => 1
  | p :: w => E p.1 p.2 * wAct E w

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def NE {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : ℝ :=
  ∑ l ∈ range (j + 1), ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖

def NT {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) : ℝ :=
  ∑ c, NE E j (f c)

def dSW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dS σ X (dSW σ w v)

def nuJ (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (v : H) : ℝ :=
  (Ws.map fun w => ‖dSW σ w v‖).sum

def DecBoundJ (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m N : ℕ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))),
    (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, inG ε X) ∧
    ∀ u v : H, IsSmoothVecU ε σ u → IsSmoothVecU ε σ v → ∀ g ∈ UJset ε,
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (σ g u)‖ ≤ C * nuJ σ Ws u * nuJ σ Ws v

end ReciprocityTheory.ChartRestriction.DS.DecInf
