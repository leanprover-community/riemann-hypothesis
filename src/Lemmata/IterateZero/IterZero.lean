module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.TaylorSeries
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

namespace Bl.IterateZero

theorem goal1 :
  ∀ (k : Nat) (g : Complex → Complex) (A : Real),
  Differentiable.{0, 0, 0} Complex g →
    (∀ (t : Complex),
        LE.le.{0} (Norm.norm.{0} (g t))
          (HMul.hMul.{0, 0, 0} A (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Norm.norm.{0} t)) k))) →
      Exists.{1} fun (P : Polynomial.{0} Complex) ↦
        And (LE.le.{0} (Polynomial.natDegree.{0} P) k) (∀ (t : Complex), Eq.{1} (g t) (Polynomial.eval.{0} t P)) := by
  intro k g A hg hb
  have hA : 0 ≤ A := by
    simpa using (norm_nonneg (g 0)).trans (hb 0)
  have hO : Asymptotics.IsBigO (Bornology.cobounded ℂ) g (fun z : ℂ => z ^ k) := by
    refine Asymptotics.IsBigO.of_bound (A * 2 ^ k) ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (1 : ℝ)] with z hz
    calc
      ‖g z‖ ≤ A * (1 + ‖z‖) ^ k := hb z
      _ ≤ A * (2 * ‖z‖) ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) k) hA
      _ = (A * 2 ^ k) * ‖z ^ k‖ := by rw [norm_pow, mul_pow, mul_assoc]
  obtain ⟨P, hP, hEq⟩ := hg.exists_eq_polynomial_eval_of_isBigO_pow hO
  exact ⟨P, hP, fun t => congrFun hEq t⟩

end Bl.IterateZero
