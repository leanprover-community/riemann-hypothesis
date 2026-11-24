module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.Alc

open Formalism.GradedWeylDivisibility

def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def shift (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : R := μ i + ((N - 1 - i.val : ℕ) : R)

def hcMat (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i l => if l = i then shift R μ i else if i < l then -1 else 0

def hcVal (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R := ∑ i, ∑ l, (hcMat R μ ^ k) i l

def rowE (R : Type) [CommRing R] (r n : ℕ) : Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n, (LinearMap.mulLeft R (X (a, s))).comp (pderiv (b, s)).toLinearMap

def gel (R : Type) [CommRing R] (r n k : ℕ) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (rowE R r n ^ k).trace

def Good {R : Type} [CommRing R] {r n : ℕ} (M : Submodule R (MvPolynomial (Fin r × Fin n) R)) : Prop :=
  (∀ a b, ∀ f ∈ M, rowE R r n a b f ∈ M) ∧
  (∀ μ : Fin r → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW r n) μ f ∈ M) ∧
  ∀ σ : Equiv.Perm (Fin r), ∀ f ∈ M, rename (fun v : Fin r × Fin n => (σ v.1, v.2)) f ∈ M


open MvPolynomial in
theorem _root_.GlobalTheory.Alc.good_top_bot (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Alc.Good (⊤ : Submodule R (MvPolynomial (Fin r × Fin n) R)) ∧ _root_.GlobalTheory.Alc.Good (⊥ : Submodule R (MvPolynomial (Fin r × Fin n) R)) := by
  refine ⟨⟨fun _ _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
    fun _ _ _ => Submodule.mem_top⟩, ⟨?_, ?_, ?_⟩⟩
  · intro a b f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro μ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro σ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]

end GlobalTheory.Alc
