module

public import ReciprocityTheory.DualLattices.VDetEqOneOfIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.TensorSpan

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) : C :=
  ∏ τ, ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

def freeMat {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : ℕ) :
    Matrix (Fin n × Fin h) (Fin n × Fin h) C :=
  Matrix.of fun x y => if x.2 = y.2 then a x.1 ^ (y.1 : ℕ) else 0

def sumPts {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ}
    (Mτ : Fin n → Lat v (Fin s)) : Set (Fin n × Fin s → C) :=
  {w | ∀ τ, (fun i => w (τ, i)) ∈ (Mτ τ).pts}

def projPts {C : Type} [Field C] {n s : ℕ} (M : Set (Fin n × Fin s → C)) (τ : Fin n) :
    Set (Fin s → C) :=
  (fun w i => w (τ, i)) '' M

def IsLaStable {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ} (a : Fin n → C)
    (M : Lat v (Fin n × Fin s)) : Prop :=
  ∀ w ∈ M.pts, (fun y : Fin n × Fin s => a y.1 * w y) ∈ M.pts

end ReciprocityTheory.PGsh.Up
