module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.BranchSandwichDivisors.StatementR
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

noncomputable section

namespace Formalism.BranchingDeterminantCap

def extM (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => if h : a.val < n ∧ b.val < n then g ⟨a.val, h.1⟩ ⟨b.val, h.2⟩
    else if a = b then 1 else 0

def rowsA {n : ℕ} (i : Fin n) : Fin (i.val + 1) → Fin (n + 1) := fun p => ⟨p.val, by omega⟩

def rowsB {n : ℕ} (i : Fin n) : Fin (i.val + 1) → Fin (n + 1) :=
  fun p => if p.val < i.val then ⟨p.val, by omega⟩ else Fin.last n

def xiB (R : Type*) [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1) × Fin n) R :=
  ∏ i : Fin n, (initMinor R (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
    initMinor R (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i))

def lamZ {n : ℕ} (lam : Fin n → ℕ) : Fin (n + 1) → ℤ :=
  fun a => if h : a.val < n then (lam ⟨a.val, h⟩ : ℤ) else 0

def weylProd {n : ℕ} (nu : Fin (n + 1) → ℤ) : ℝ :=
  ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
    (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
      (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ))

def BranchMap : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (lam sg : Fin n → ℕ),
    Interlace (lamZ lam) (fun i => (sg i : ℤ)) →
    ∃ io : ↥(dualWeyl R n n sg) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R,
      (∀ f, io f ∈ dualWeyl R (n + 1) n lam) ∧
      (∀ (g : Matrix (Fin n) (Fin n) R) (f f' : ↥(dualWeyl R n n sg)),
        (f' : MvPolynomial (Fin n × Fin n) R) = rowAct R g (f : MvPolynomial (Fin n × Fin n) R) →
          io f' = rowAct R (extM R g) (io f)) ∧
      (∀ h : ↥(dualWeyl R n n sg), (h : MvPolynomial (Fin n × Fin n) R) = hw R le_rfl sg →
        io h = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg) ∧
      (∀ f, ∀ m ∈ (io f).support, rowDeg m (Fin.last n) = ∑ i, (lam i - sg i))

def XiNorm : Prop :=
  ∀ (n : ℕ) (lam sg : Fin n → ℕ), Interlace (lamZ lam) (fun i => (sg i : ℤ)) →
    (fockF (xiB ℂ lam sg) (xiB ℂ lam sg)).re ≤
      weylProd (lamZ lam) * (fockF (hw ℂ (Nat.le_succ n) lam) (hw ℂ (Nat.le_succ n) lam)).re

end Formalism.BranchingDeterminantCap
