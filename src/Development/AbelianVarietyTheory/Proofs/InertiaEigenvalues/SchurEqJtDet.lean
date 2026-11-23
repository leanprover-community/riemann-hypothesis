module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

def padTo {m n : ℕ} (_h : m ≤ n) (l : Fin m → ℕ) : Fin n → ℕ :=
  fun i => if hi : (i : ℕ) < m then l ⟨i, hi⟩ else 0


open Classical in
def antiParts (m d : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m d).filter Antitone

def jtDet {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) : A :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat))

def staircase (m : ℕ) : Fin m → ℕ := fun i => m - 1 - i

def alternant (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) : MvPolynomial (Fin m) A :=
  Matrix.det (Matrix.of fun i j : Fin m => (MvPolynomial.X j : MvPolynomial (Fin m) A) ^ μ i)

theorem schur_eq_jtDet (n : ℕ) (l : Fin n → ℕ) :
    schur n l = jtDet n (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := rfl

theorem mem_antiParts {m d : ℕ} {l : Fin m → ℕ} : l ∈ antiParts m d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

theorem padTo_self {m : ℕ} (l : Fin m → ℕ) : padTo le_rfl l = l := by
  funext i; simp [padTo, i.2]

end GlobalTheory.JSW
