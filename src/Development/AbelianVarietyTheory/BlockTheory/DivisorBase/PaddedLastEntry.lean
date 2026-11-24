module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def ph (y : ℝ) : ℝ := y * Real.log y - y

def size {a : ℕ} (nu : DomWeight a) : ℕ := ∑ i, (nu.w i).toNat

def lastEntry {a : ℕ} (nu : DomWeight a) : ℕ := nu.detShift.toNat

def padZero {a : ℕ} (b : ℕ) (nu : DomWeight a) (j : Fin b) : ℤ :=
  if h : j.1 < a then nu.w ⟨j.1, h⟩ else 0

def StepWeights {a b : ℕ} (lam nu : DomWeight a) (lam' : DomWeight b) : Prop :=
  (∀ i, 0 ≤ nu.w i) ∧ (∃ s' : ℤ, ∀ i, nu.w i = lam.w i + s') ∧
    ∃ s : ℤ, ∀ j, lam'.w j + s = padZero b nu j

def invNormSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (P : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P P).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ P : VV ℂ lam, invNormSq lam' (T P) ≤ t * invNormSq lam P

def unitSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (nu : ι → DomWeight a) (S : ℝ) (Om : ι → ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ size (nu τ) * Real.exp 1 * (2 * (size (nu τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, ph ((nu τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b),
    (∀ τ, StepWeights (lam τ) (nu τ) (lam' τ)) →
    (a = b → ∀ τ, lastEntry (nu τ) = 0) →
  ∀ (r Om : ι → ℝ) (cD : ι → ℂ),
    (∀ τ, 0 < r τ) → (∀ τ, 0 < Om τ) → (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ), Differentiable ℂ G →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitSq r z / 2)) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (nu τ)) (tmax b nu S Om)

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry
