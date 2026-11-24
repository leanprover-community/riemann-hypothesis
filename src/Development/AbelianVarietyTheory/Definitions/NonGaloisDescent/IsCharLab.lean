module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
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

namespace GlobalTheory.GLp

open Polynomial GlobalTheory.GLq
open scoped Classical

variable (g : ℕ) [Fact g.Prime]

def inc (n : ℕ) : GL (Fin n) ℤ_[g] →* GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g])

def red (n : ℕ) : GL (Fin n) ℤ_[g] →* Gn g n := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g))

def lift (n : ℕ) (x : Gn g n) : GL (Fin n) ℚ_[g] := inc g n (Function.invFun (red g n) x)

variable {g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def fixK1 (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Submodule ℂ V :=
  ⨅ k : (red g n).ker, LinearMap.ker (π (inc g n k) - LinearMap.id)

def actK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g n, a.coeff x • π (lift g n x)

def IsIrrRep {G : Type} [Group G] (π : Representation ℂ G V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, π x v ∈ W) → W = ⊥ ∨ W = ⊤

def blk (a b n : ℕ) (x : Gn g a) (y : Gn g b) : Gn g n :=
  toG (fun i j : Fin n =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then Formalism.MainNotions.ArithmeticCylinders.entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g b) (i - a) (j - a) else 0)

def IsParVec (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (v : V) : Prop :=
  v ∈ fixK1 π ∧
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → π (lift g n u) v = v) ∧
    ∀ y : Gn g b, π (lift g n (blk a b n 1 y)) v = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v

def actTop (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (e : MonoidAlgebra ℂ (Gn g a)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g a, e.coeff x • π (lift g n (blk a b n x 1))

def IsCharLab (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) : Prop :=
  c ≠ 0 ∧ ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
    ((χ u : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)

end GlobalTheory.GLp
