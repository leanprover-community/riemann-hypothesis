module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
public import Mathlib.Analysis.Matrix.Normed
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

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)

def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F

def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F

def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R

def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}

def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}

def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M

def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)

def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))

def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b

end PositivityTheory.Rg.Sw.WR.K.GB
