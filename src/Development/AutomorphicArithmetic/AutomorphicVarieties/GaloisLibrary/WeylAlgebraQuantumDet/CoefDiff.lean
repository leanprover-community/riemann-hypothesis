module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.differentiable_eval_polynomial_entries (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; fun_prop
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p ab hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop)

theorem UpperTheory.V.Weyl.coefDiff :
    ∀ (n : ℕ) (Ξ : Pre n) (i j : Fin Ξ.d), Differentiable ℂ (Ξ.coef i j) := by
  intro n Ξ i j
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p := by
    funext x
    exact hp (Matrix.of x)
  rw [h]
  exact UpperTheory.V.Weyl.differentiable_eval_polynomial_entries n p
