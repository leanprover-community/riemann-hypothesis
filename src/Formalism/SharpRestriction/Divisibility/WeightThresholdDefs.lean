module

public import Formalism.SharpRestriction.Divisibility.PrinLevClass
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

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
