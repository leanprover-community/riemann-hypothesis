module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
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

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

abbrev MC (n : ℕ) := Fin n → Fin n → ℂ

def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0

def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)

def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}

def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R

def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y

def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)

end PositivityTheory.Rg.Sw.WR.Z
