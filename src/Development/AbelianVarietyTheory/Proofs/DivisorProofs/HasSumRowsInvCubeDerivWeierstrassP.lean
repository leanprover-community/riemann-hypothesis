module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
