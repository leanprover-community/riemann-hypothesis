module

public import Formalism.HermitianCurvature.StatementB
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.BigCellVanishingOfCommute

@[expose] public section

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def hW (k : ℕ) (j : Fin (k + 1)) : ℂ := if j.val = k then -1 else 1

def zW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => z (wI k r j)

def cmOf (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  S - (1 / 2 : ℂ) • (Bm * Matrix.diagonal (hW k) * Bmᴴ)

def unipotentBlockMatrix (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r :=
  Matrix.of fun i j =>
    (if i = j then 1 else 0) +
    (if h : i.val < r ∧ r ≤ j.val ∧ j.val ≤ r + k then
      Bm ⟨i.val, h.1⟩ ⟨j.val - r, by omega⟩ else 0) +
    (if h : i.val < r ∧ r + k < j.val then
      cmOf k r Bm S ⟨i.val, h.1⟩ ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ else 0) +
    (if h : r ≤ i.val ∧ i.val ≤ r + k ∧ r + k < j.val then
      -(hW k ⟨i.val - r, by omega⟩) * star (Bm ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ ⟨i.val - r, by omega⟩)
      else 0)

end PI.UnitaryGroupMassFormula.DLm
