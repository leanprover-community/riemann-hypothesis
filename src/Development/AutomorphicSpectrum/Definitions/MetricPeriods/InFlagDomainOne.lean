module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
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

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

def gramOf {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  gᴴ * diagonal (fun i => (hd i : ℂ)) * g

def gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    Matrix {a : Fin N // (a : ℕ) < k} {a : Fin N // (a : ℕ) < k} ℂ :=
  (gramOf hd g).submatrix Subtype.val Subtype.val

def gramLog {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / 2) * Real.log ‖(gramHead hd k g).det‖

def sigForm (N j : ℕ) : Fin N → ℝ := fun a => if (a : ℕ) < N - j then -1 else 1

def InFlagDomain (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsUnit g.det ∧ (-gramHead (sigForm N j) (N - j) g).PosDef

def stepPot (N j : ℕ) (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) g - gramLog (sigForm N j) (N - j) g
  else gramLog (sigForm N j) N g - gramLog (sigForm N j) (N - j) g + gramLog (sigForm N j) ((i : ℕ) + 1 - j) g

def herm2 (G : Matrix (Fin 2) (Fin 2) ℂ) (u w : Fin 2 → ℂ) : ℂ := star u ⬝ᵥ (G *ᵥ w)

def xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℝ :=
  -Real.log (herm2 G ![1, a] ![1, a]).re + (1 / 2) * Real.log G.det.re

def logSin (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) : ℝ :=
  (1 / 2) * Real.log (1 - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 /
    ((herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re))

end GlobalTheory.CompanionTheory.Ar.PB
