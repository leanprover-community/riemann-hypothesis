module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

namespace GlobalTheory.UTrans

variable {R : Type} [CommRing R] {n : ℕ}

def hf (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) : R :=
  ∑ a, ∑ b, x a * G a b * σ (y b)

def IsU (σ : R →+* R) (G γ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ x y, hf σ G (γ.mulVec x) (γ.mulVec y) = hf σ G x y

def tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) : Matrix (Fin n) (Fin n) R :=
  1 + Matrix.of fun a b => t * x a * ∑ e, G b e * σ (x e)

def TvGen (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) : Submonoid (Matrix (Fin n) (Fin n) R) :=
  Submonoid.closure {m | ∃ x t, hf σ G x x = 0 ∧ t + σ t = 0 ∧ m = tv σ G x t}

structure IsHerm {E : Type} [Field E] (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) : Prop where
  invol : ∀ a, σ (σ a) = a
  ne_id : ∃ a, σ a ≠ a
  herm : ∀ a b, σ (G a b) = G b a
  det_ne : G.det ≠ 0

end GlobalTheory.UTrans
