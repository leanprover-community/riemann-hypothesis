module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem differentiable_class_function_param (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) :
    Differentiable ℂ (fun z : ℂ => clsC s z p q R B) := by
  unfold clsC
  fun_prop

theorem factor (hE : Ext) (hCh : Chain) (hBr : Bridge) {s : ℂ} (hs : s = 1 ∨ s = -1) (m N r : ℕ)
    (hdiv : DivZ r ((cayF (n := n) s m)^[N] 1)) (y : E n) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, (Delta^[N] (cls s z m 0 1)) y = z ^ r * q z := by
  obtain ⟨hO, hherm, han⟩ := hE n s hs
  set P : Fm n := (cayF (n := n) s m)^[N] 1 with hP
  choose d hd using hdiv
  set v : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2
    else (1 - (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2 with hv
  refine ⟨fun z => clsC s z m 0 1 (herm y) * ∑ e ∈ P.support, (d e).eval z * ∏ i ∈ e.support, v i ^ e i, ?_, ?_⟩
  · refine (differentiable_class_function_param s m 0 1 _).mul ?_
    exact Differentiable.fun_sum fun e _ => (Polynomial.differentiable _).mul (differentiable_const _)
  · intro z
    have hcls : cls s z m 0 1 = fun y : E n => clsC s z m 0 1 (herm y) := funext fun y => ((han z m 0 1).2 y).symm
    rw [hcls, hCh n (OmS s) (clsC s z m 0 1) hO hherm (han z m 0 1).1 N y, hBr n s hs m N z (herm y) (hherm y)]
    rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
    simp only [← hv, ← hP, Polynomial.coe_evalRingHom]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hd e, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring

end PositivityTheory.Rg.Sw.SP
