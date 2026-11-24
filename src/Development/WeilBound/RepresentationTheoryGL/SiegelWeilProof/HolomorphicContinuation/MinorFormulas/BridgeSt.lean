module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
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

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def Ym (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • Matrix.of B)⁻¹

def Yp (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • Matrix.of B)⁻¹

def vals (s : ℂ) (B : MC n) : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then Yp s B k.2.1 k.2.2 else Ym s B k.2.1 k.2.2

def evQ (s z : ℂ) (Q : Fm n) (B : MC n) : ℂ :=
  MvPolynomial.eval (vals s B) (MvPolynomial.map (Polynomial.evalRingHom z) Q)

def fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B : MC n) : ℂ := clsC s z m 0 1 B * evQ s z Q B

def HYm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 - (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Ym s (x + t • v) a d) (((Complex.I * s) • (Ym s x * Matrix.of v * Ym s x)) a d) 0

def HYp : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 + (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Yp s (x + t • v) a d) ((-(Complex.I * s) • (Yp s x * Matrix.of v * Yp s x)) a d) 0

def HCls : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (z : ℂ) (m : ℕ) (x v : MC n), x ∈ OmS s →
    HasDerivAt (fun t : ℂ => clsC s z m 0 1 (x + t • v))
      (clsC s z m 0 1 x * (Complex.I * s * ((m : ℂ) + z) * (Ym s x * Matrix.of v).trace -
        Complex.I * s * z * (Yp s x * Matrix.of v).trace)) 0

end PositivityTheory.Rg.Sw.SP
