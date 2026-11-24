module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ
    refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ
    obtain ⟨p1, h1⟩ := hp φ
    obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _)]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n =>
      hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n)
        = ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by
      simp [rtr, MvPolynomial.aeval_X]

    rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2))
        = MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
