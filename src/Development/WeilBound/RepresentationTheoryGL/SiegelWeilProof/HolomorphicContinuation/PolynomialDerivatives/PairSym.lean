module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
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

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def EtaLt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) < N

def EtaLe (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) ≤ N

def vecVar (ε : Fin m → Bool) (a : Fin m) (i : Fin n) : Sym m n :=
  if ε a then X (Sum.inl (a, i, false)) else X (Sum.inr (a, i, true))

def covVar (ε : Fin m → Bool) (b : Fin m) (i : Fin n) : Sym m n :=
  if ε b then X (Sum.inr (b, i, false)) else X (Sum.inl (b, i, true))

def pairSym (ε : Fin m → Bool) (a b : Fin m) : Sym m n := ∑ i, vecVar ε a i * covVar ε b i

def CompSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (u v : Sym m n) (d₁ d₂ : ℕ), SymbolInFirstFamily ε u → SymbolInFirstFamily ε v → EtaLe u d₁ → EtaLe v d₂ →
    ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r (d₁ + d₂) ∧ ∀ f, op u (op v f) = op (u * v) f + op r f

def FFTSym : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    s ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => (pairSym (n := n) ε ab.1 ab.2))

end PositivityTheory.Rg.Sw.LC
