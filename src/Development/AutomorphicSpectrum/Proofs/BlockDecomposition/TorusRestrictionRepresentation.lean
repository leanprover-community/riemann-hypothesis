module

public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
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

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
