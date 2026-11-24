module

public import Formalism.LocalRingCardinality.DataTheta
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

open MvPolynomial Formalism.BasicNotions

namespace UpperTheory.TP.RP

abbrev PP (n d : ℕ) : Type := Formalism.BasicNotions.TH.Pol n 0 d 0

def xv {n d : ℕ} (i : Fin n) (j : Fin d) : PP n d := X (Sum.inl i, Sum.inl j)

def leftSub {n d : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : PP n d →ₐ[ℂ] PP n d :=
  aeval fun l => match l with
    | (Sum.inl b, Sum.inl c) => ∑ a, C (g a b) * xv a c
    | l => X l

def rightSub {n d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) : PP n d →ₐ[ℂ] PP n d :=
  aeval fun l => match l with
    | (Sum.inl b, Sum.inl c) => ∑ a, C (h a c) * xv b a
    | l => X l

def act1 {n d : ℕ} (c : ℤ) (g : GL (Fin n) ℂ) : Module.End ℂ (PP n d) :=
  detPow ℂ n g c • (leftSub g.1).toLinearMap

def act2 {n d : ℕ} (c : ℤ) (h : GL (Fin d) ℂ) : Module.End ℂ (PP n d) :=
  detPow ℂ d h c • (rightSub h.1).toLinearMap

def ofTall {n d : ℕ} : MvPolynomial (Fin d × Fin n) ℂ →ₐ[ℂ] PP n d := rename fun v => (Sum.inl v.2, Sum.inl v.1)

def joint {n d : ℕ} (h : n ≤ d) (μ : Fin n → ℕ) : PP n d := ofTall (Formalism.GradedWeylDivisibility.hw ℂ h μ)

end UpperTheory.TP.RP

end
