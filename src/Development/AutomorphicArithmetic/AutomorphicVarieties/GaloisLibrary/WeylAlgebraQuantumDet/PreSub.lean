module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ :=
    UpperTheory.V.Weyl.subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly
    intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]

    simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := by
    intro a b
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := UpperTheory.V.Weyl.curve n Ξ _ X h0 hc
  have h2 := UpperTheory.V.Weyl.curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1
  exact e1.unique e2
