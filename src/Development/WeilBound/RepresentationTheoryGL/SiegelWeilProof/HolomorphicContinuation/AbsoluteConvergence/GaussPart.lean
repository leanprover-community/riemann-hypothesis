module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def bS (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun j => (Real.exp (-(h * X j)) : ℂ)) * b * diagonal (fun j => (Real.exp (-(h * X j)) : ℂ))

def GaussPart : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (X : Fin n → ℝ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    ∀ Q : PX m n, HasDerivAt (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b))
      (secN ε c t (dil c X Q) b) 0

def GroupPart : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    (∀ s s', a (s + s') = a s * a s') ∧ a 0 = 1 ∧ (∀ s, IsUp (a s)) ∧ Continuous a ∧
    (∀ y : GR n, IsUp y → ∀ s, IsUp (y * a s)) ∧
    (∀ (y : GR n), (mR y).toBlocks₂₁.det ≠ 0 → ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
      mR g = JJ n * nU b ∧ y = y₁ * g) ∧
    (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), mR g = JJ n * nU b → ∀ h, mR (a h * g * a h) = JJ n * nU (bS X h b)) ∧
    (∀ y : GR n, (mR y).toBlocks₂₁.det ≠ 0 → ∀ s, (mR (y * a s)).toBlocks₂₁.det ≠ 0) ∧
    Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} ∧
    ∀ (p q : ℕ) (e : ℤ) (h : ℝ), F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ))

end PositivityTheory.Rg.Sw.AbsSt.DF
